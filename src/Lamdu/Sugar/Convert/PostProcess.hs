{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Sugar.Convert.PostProcess
    ( PostProcessResult(..), postProcessDef, postProcessExpr
    ) where

import qualified Data.Store.Property as Property
import           Data.Store.Transaction (Transaction)
import qualified Data.Store.Transaction as Transaction
import qualified Lamdu.Calc.Val.Annotated as Val
import qualified Lamdu.Data.Definition as Definition
import           Lamdu.Expr.IRef (DefI, ValI)
import qualified Lamdu.Expr.IRef as ExprIRef
import qualified Lamdu.Infer as Infer
import qualified Lamdu.Infer.Error as InferErr
import qualified Lamdu.Sugar.Convert.Load as Load

import           Lamdu.Prelude

type T = Transaction

data PostProcessResult = GoodExpr | BadExpr InferErr.Error

postProcessDef :: Monad m => DefI m -> T m PostProcessResult
postProcessDef defI =
    do
        def <- Transaction.readIRef defI
        case def ^. Definition.defBody of
            Definition.BodyBuiltin {} -> pure GoodExpr
            Definition.BodyExpr defExpr ->
                do
                    loaded <- Definition.expr ExprIRef.readVal defExpr
                    checked <- Load.inferCheckDef loaded (ExprIRef.globalId defI)
                    case checked of
                        Left err -> BadExpr err & pure
                        Right (inferredVal, inferContext) ->
                            GoodExpr <$
                            ( def
                            & Definition.defType .~
                                Infer.makeScheme inferContext inferredType
                            & Definition.defBody . Definition._BodyExpr .
                                Definition.exprFrozenDeps .~
                                Definition.pruneDefExprDeps loaded
                            & Transaction.writeIRef defI
                            )
                            where
                                inferredType = inferredVal ^. Val.payload . _1 . Infer.plType

postProcessExpr ::
    Monad m =>
    Transaction.MkProperty m (Definition.Expr (ValI m)) ->
    T m PostProcessResult
postProcessExpr mkProp =
    do
        prop <- mkProp ^. Transaction.mkProperty
        -- TODO: This is code duplication with the above Load.inferDef
        -- & functions inside Load itself
        defExpr <- Definition.expr ExprIRef.readVal (prop ^. Property.pVal)
        inferred <- Load.inferCheckDefExpr defExpr
        case inferred of
            Left err -> BadExpr err & pure
            Right _ ->
                GoodExpr <$
                Property.pureModify prop
                (Definition.exprFrozenDeps .~ Definition.pruneDefExprDeps defExpr)

