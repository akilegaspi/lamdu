-- | Build sugar expressions easily

module Test.Lamdu.SugarStubs where

import           Control.Monad.Unit (Unit(Unit))
import           Data.CurAndPrev (CurAndPrev(CurAndPrev))
import           Data.Functor.Identity (Identity)
import           Data.Property (Property(Property))
import           Data.String (IsString(..))
import           Data.UUID.Types (UUID)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Sugar.Internal (nameWithoutContext)
import           Lamdu.Sugar.Names.Add (InternalName(..))
import qualified Lamdu.Sugar.Types as Sugar
import           Test.Lamdu.Instances ()

import           Lamdu.Prelude

infixr 1 ~>
(~>) :: Sugar.Type name -> Sugar.Type name -> Sugar.Type name
param ~> res = Sugar.TFun param res & Sugar.Type "dummy"

fieldParams :: [(T.Tag, Sugar.Type InternalName)] -> Sugar.Type InternalName
fieldParams fields =
    Sugar.CompositeFields
    { Sugar._compositeFields = fields <&> _1 %~ tagInfo Nothing
    , Sugar._compositeExtension = Nothing
    } & Sugar.TRecord & Sugar.Type "dummy"

nameRef :: name -> Sugar.NameRef name Unit
nameRef = (`Sugar.NameRef` Unit)

prop :: a -> Property Unit a
prop x = Property x (const Unit)

type Expr = Sugar.Expression InternalName Identity Unit ()

litNum :: Double -> Expr
litNum x = prop x & Sugar.LiteralNum & Sugar.BodyLiteral & expr numType

defRef :: String -> T.Tag -> Sugar.BinderVarRef InternalName Unit
defRef var tag =
    Sugar.BinderVarRef
    { Sugar._bvNameRef = nameRef (taggedEntityName (fromString var) tag)
    , Sugar._bvForm = Sugar.GetDefinition Sugar.DefUpToDate
    , Sugar._bvVar = fromString var
    , Sugar._bvInline = Sugar.CannotInline
    }

labeledApplyFunc ::
    Sugar.Type name -> Sugar.BinderVarRef name Unit ->
    Sugar.LabeledApplyFunc name Identity Unit ()
labeledApplyFunc typ varRef =
    Sugar.LabeledApplyFunc
    { Sugar._afVar = varRef
    , Sugar._afPayload = mkPayload typ
    }

type Infix2 = Expr -> Expr -> Expr

infix2Apply ::
    Sugar.Type InternalName ->
    Sugar.BinderVarRef InternalName Unit ->
    T.Tag -> T.Tag -> Infix2
infix2Apply resTyp varRef lTag rTag l r =
    Sugar.LabeledApply (labeledApplyFunc funcType varRef) (Sugar.Infix l r) [] []
    & Sugar.BodyLabeledApply
    & expr resTyp
    where
        exprType = Sugar.rPayload . Sugar.plAnnotation . Sugar.aInferredType
        funcType = params ~> resTyp
        params = fieldParams [(lTag, lType), (rTag, rType)]
        lType = l ^. exprType
        rType = r ^. exprType

arithmeticInfix2 :: String -> Infix2
arithmeticInfix2 op =
    infix2Apply numType (defRef (fromString op) (fromString op))
    "infixl" "infixr"

plus :: Infix2
plus = arithmeticInfix2 "+"

mul :: Infix2
mul = arithmeticInfix2 "*"

pane ::
    Sugar.Definition name i Unit (Sugar.Expression name i Unit a) ->
    Sugar.Pane name i Unit a
pane body =
    Sugar.Pane
    { Sugar._paneDefinition = body
    , Sugar._paneClose = Unit
    , Sugar._paneMoveDown = Nothing
    , Sugar._paneMoveUp = Nothing
    }

tagInfo :: Maybe UUID -> T.Tag -> Sugar.TagInfo InternalName
tagInfo var tag =
    Sugar.TagInfo
    { Sugar._tagName = maybe nameWithoutContext taggedEntityName var tag
    , Sugar._tagInstance = "dummy"
    , Sugar._tagVal = tag
    }

mkTag :: UUID -> T.Tag -> Sugar.Tag InternalName Identity Unit
mkTag var tag =
    Sugar.Tag
    { Sugar._tagSelection = tagSelection
    , Sugar._tagInfo = tagInfo (Just var) tag
    }

def ::
    Sugar.Type InternalName -> UUID -> T.Tag ->
    Sugar.Binder InternalName Identity Unit expr ->
    Sugar.Definition InternalName Identity Unit expr
def typ var tag body =
    Sugar.Definition
    { Sugar._drName = mkTag var tag
    , Sugar._drDefI = "def"
    , Sugar._drDefinitionState = prop Sugar.LiveDefinition & pure
    , Sugar._drEntityId = "dummy"
    , Sugar._drBody =
        Sugar.DefinitionBodyExpression Sugar.DefinitionExpression
        { Sugar._deType =
            Sugar.Scheme
            { Sugar._schemeForAll = mempty
            , Sugar._schemeConstraints = mempty
            , Sugar._schemeType = typ
            }
        , Sugar._dePresentationMode = Nothing
        , Sugar._deContent = body
        }
    }

repl :: Sugar.Expression name i o a -> Sugar.Repl name i o a
repl x =
    Sugar.Repl
    { Sugar._replExpr = x
    , Sugar._replResult = CurAndPrev Nothing Nothing
    }

mkFuncParam ::
    (UUID, T.Tag, Sugar.Type name) ->
    Sugar.FuncParam name (Sugar.ParamInfo InternalName Identity Unit)
mkFuncParam (paramVar, paramTag, paramType) =
    Sugar.FuncParam
    { Sugar._fpAnnotation = annotation paramType
    , Sugar._fpInfo =
        Sugar.ParamInfo
        { Sugar._piTag = mkTag paramVar paramTag
        , Sugar._piActions =
            Sugar.FuncParamActions
            { Sugar._fpAddNext = Sugar.AddNext tagSelection
            , Sugar._fpDelete = Unit
            , Sugar._fpMOrderBefore = Nothing
            , Sugar._fpMOrderAfter = Nothing
            }
        }
    }

binderExpr ::
    [(UUID, T.Tag, Sugar.Type InternalName)] -> Expr ->
    Sugar.Binder InternalName Identity Unit Expr
binderExpr params body =
    Sugar.Binder
    { Sugar._bChosenScopeProp = prop Nothing & pure
    , Sugar._bLamId =
        case params of
        [] -> Nothing
        _:_ -> Just "dummy"
    , Sugar._bBodyScopes = CurAndPrev mempty mempty & Sugar.BinderBodyScope
    , Sugar._bActions =
        Sugar.BinderActions
        { Sugar._baAddFirstParam = Sugar.PrependParam tagSelection
        , Sugar._baMNodeActions = Just nodeActions
        }
    , Sugar._bParams = params <&> mkFuncParam & Sugar.Params
    , Sugar._bBody =
        Sugar.BinderBody
        { Sugar._bbAddOuterLet = Unit
        , Sugar._bbContent = Sugar.BinderExpr body
        }
    }

expr ::
    Sugar.Type name ->
    Sugar.Body name Identity Unit
    (Sugar.Expression name Identity Unit ()) ->
    Sugar.Expression name Identity Unit ()
expr typ body =
    Sugar.Expression { Sugar._rBody = body, Sugar._rPayload = mkPayload typ }

numType :: Sugar.Type InternalName
numType =
    Sugar.Type
    { Sugar._tPayload = "dummy"
    , Sugar._tBody = Sugar.TInst (Sugar.TId (taggedEntityName "numTid" "num") "num") mempty
    }

mkPayload :: Sugar.Type name -> Sugar.Payload name Identity Unit ()
mkPayload typ =
    Sugar.Payload
    { Sugar._plAnnotation = annotation typ
    , Sugar._plEntityId = "dummy"
    , Sugar._plActions = nodeActions
    , Sugar._plData = ()
    }

annotation :: Sugar.Type name -> Sugar.Annotation name
annotation typ =
    Sugar.Annotation
    { Sugar._aInferredType = typ
    , Sugar._aMEvaluationResult = CurAndPrev Nothing Nothing
    }

nodeActions :: Sugar.NodeActions name Identity Unit
nodeActions =
    Sugar.NodeActions
    { Sugar._detach = Sugar.DetachAction Unit
    , Sugar._mSetToHole = Nothing
    , Sugar._extract = Unit
    , Sugar._mReplaceParent = Nothing
    , Sugar._wrapInRecord = tagSelection
    }

taggedEntityName :: UUID -> T.Tag -> InternalName
taggedEntityName ctx tag =
    InternalName
    { _inContext = Just ctx
    , _inTag = tag
    }

tagSelection :: Sugar.TagSelection name Identity Unit ()
tagSelection =
    Sugar.TagSelection
    { Sugar._tsOptions = pure []
    , Sugar._tsNewTag = const Unit
    , Sugar._tsAnon = Nothing
    }