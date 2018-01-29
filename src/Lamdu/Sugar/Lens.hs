{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RecordWildCards, RankNTypes #-}
module Lamdu.Sugar.Lens
    ( subExprPayloads, payloadsIndexedByPath
    , payloadsOf
    , bodyUnfinished, unfinishedExprPayloads, fragmentExprs
    , defSchemes
    , binderFuncParamActions
    , binderFuncParamAdds
    , binderFuncParamDeletes
    , binderContentExpr
    , binderContentEntityId
    , leftMostLeaf
    , workAreaExpressions
    ) where

import qualified Control.Lens as Lens
import           Lamdu.Calc.Type.Scheme (Scheme)
import           Lamdu.Sugar.Types

import           Lamdu.Prelude

subExprPayloads ::
    Lens.IndexedTraversal
    (Expression name m ())
    (Expression name m a)
    (Expression name m b)
    (Payload m a) (Payload m b)
subExprPayloads f val@(Expression body pl) =
    Expression
    <$> (Lens.traversed .> subExprPayloads) f body
    <*> Lens.indexed f (void val) pl

payloadsIndexedByPath ::
    Lens.IndexedTraversal
    [Expression name m ()]
    (Expression name m a)
    (Expression name m b)
    (Payload m a) (Payload m b)
payloadsIndexedByPath f =
    go []
    where
        go path val@(Expression body pl) =
            Expression
            <$> Lens.traversed (go newPath) body
            <*> Lens.indexed f newPath pl
            where
                newPath = void val : path

payloadsOf ::
    Lens.Fold (Body name m (Expression name m ())) a ->
    Lens.IndexedTraversal'
    (Expression name m ())
    (Expression name m b)
    (Payload m b)
payloadsOf body =
    subExprPayloads . Lens.ifiltered predicate
    where
        predicate idx _ = Lens.has (rBody . body) idx

binderVarRefUnfinished :: Lens.Traversal' (BinderVarRef name m) ()
binderVarRefUnfinished =
    bvForm . _GetDefinition . Lens.failing _DefDeleted (_DefTypeChanged . Lens.united)

bodyUnfinished :: Lens.Traversal' (Body name m a) ()
bodyUnfinished =
    _BodyHole . Lens.united
    & Lens.failing (_BodyFragment . Lens.united)
    & Lens.failing (_BodyGetVar . _GetBinder . binderVarRefUnfinished)
    & Lens.failing (_BodyLabeledApply . aFunc . binderVarRefUnfinished)

unfinishedExprPayloads ::
    Lens.IndexedTraversal'
    (Expression name m ())
    (Expression name m a)
    (Payload m a)
unfinishedExprPayloads = payloadsOf bodyUnfinished

subExprsOf ::
    Lens.Traversal' (Body name m (Expression name m ())) b ->
    Lens.IndexedTraversal'
    [Expression name m ()]
    (Expression name m a)
    (Payload m a)
subExprsOf f =
    payloadsIndexedByPath . Lens.ifiltered predicate
    where
        predicate (_:parent:_) _ = Lens.has (rBody . f) parent
        predicate _ _ = False

fragmentExprs ::
    Lens.IndexedTraversal'
    [Expression name m ()]
    (Expression name m a)
    (Payload m a)
fragmentExprs = subExprsOf _BodyFragment

defBodySchemes :: Lens.Traversal' (DefinitionBody name m expr) Scheme
defBodySchemes f (DefinitionBodyBuiltin b) =
    b & biType %%~ f
    <&> DefinitionBodyBuiltin
defBodySchemes f (DefinitionBodyExpression de) =
    de & deType %%~ f
    <&> DefinitionBodyExpression

defSchemes :: Lens.Traversal' (Definition name m expr) Scheme
defSchemes = drBody . defBodySchemes

binderFuncParamActions ::
    Lens.Traversal' (BinderParams name m) (FuncParamActions m)
binderFuncParamActions _ BinderWithoutParams = pure BinderWithoutParams
binderFuncParamActions _ (NullParam a) = pure (NullParam a)
binderFuncParamActions f (VarParam p) = (fpInfo . vpiActions) f p <&> VarParam
binderFuncParamActions f (FieldParams ps) = (traverse . fpInfo . fpiActions) f ps <&> FieldParams

binderFuncParamAdds ::
    Lens.Traversal'
    (Binder name m (Expression name m a))
    (m ParamAddResult)
binderFuncParamAdds f Binder{..} =
    (\_bParams _bActions -> Binder{..})
    <$> (_bParams & binderFuncParamActions . fpAddNext %%~ f)
    <*> (_bActions & baAddFirstParam %%~ f)

binderFuncParamDeletes ::
    Lens.Traversal'
    (Binder name m (Expression name m a))
    (m ParamDelResult)
binderFuncParamDeletes = bParams . binderFuncParamActions . fpDelete

binderContentExpr :: Lens' (BinderContent name m a) a
binderContentExpr f (BinderLet l) = l & lBody . bbContent . binderContentExpr %%~ f <&> BinderLet
binderContentExpr f (BinderExpr e) = f e <&> BinderExpr

binderContentEntityId ::
    Lens' (BinderContent name m (Expression name m a)) EntityId
binderContentEntityId f (BinderExpr e) =
    e & rPayload . plEntityId %%~ f <&> BinderExpr
binderContentEntityId f (BinderLet l) =
    l & lEntityId %%~ f <&> BinderLet

leftMostLeaf :: Expression name m a -> Expression name m a
leftMostLeaf val =
    case val ^.. rBody . Lens.traversed of
    [] -> val
    (x:_) -> leftMostLeaf x

workAreaExpressions ::
    Lens.Traversal
    (WorkArea name m a) (WorkArea name m b)
    (Expression name m a) (Expression name m b)
workAreaExpressions f (WorkArea panes repl) =
    WorkArea
    <$> (traverse . paneDefinition . traverse) f panes
    <*> f repl
