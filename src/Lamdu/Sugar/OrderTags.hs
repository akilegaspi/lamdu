{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, DefaultSignatures, ScopedTypeVariables #-}

module Lamdu.Sugar.OrderTags
    ( orderDef, orderType, orderNode
    , orderedClosedFlatComposite
    ) where

import           AST (Node, Children(..), Ann(..), monoChildren)
import qualified Control.Lens.Extended as Lens
import           Data.List (sortOn)
import           Data.Proxy (Proxy(..))
import qualified Lamdu.Calc.Type as T
import           Lamdu.Data.Tag (tagOrder)
import qualified Lamdu.Expr.IRef as ExprIRef
import qualified Lamdu.Sugar.Lens as SugarLens
import qualified Lamdu.Sugar.Types as Sugar
import           Revision.Deltum.Transaction (Transaction)

import           Lamdu.Prelude

type T = Transaction
type OrderT m x = x -> T m x

class Order m name o t where
    order :: OrderT m (t (Ann (Sugar.Payload name i o a)))

    default order ::
        ( Monad m, Children t
        , ChildrenConstraint t (Order m name o)
        ) =>
        OrderT m (t (Ann (Sugar.Payload name i o a)))
    order = children (Proxy :: Proxy (Order m name o)) orderNode

orderByTag :: Monad m => (a -> Sugar.TagInfo name) -> OrderT m [a]
orderByTag toTag =
    fmap (map fst . sortOn snd) . traverse loadOrder
    where
        loadOrder x =
            toTag x ^. Sugar.tagVal
            & ExprIRef.readTagInfo
            <&> (,) x . (^. tagOrder)

orderComposite :: Monad m => OrderT m (Sugar.CompositeFields p name (Sugar.Type a))
orderComposite =
    Sugar.compositeFields $
    \fields -> fields & orderByTag (^. _1) >>= traverse . _2 %%~ orderType

orderTBody :: Monad m => OrderT m (Sugar.TBody name (Sugar.Type name))
orderTBody t =
    t
    & Sugar._TRecord %%~ orderComposite
    >>= Sugar._TVariant %%~ orderComposite
    >>= traverse orderType

orderType :: Monad m => OrderT m (Sugar.Type name)
orderType = Sugar.tBody orderTBody

orderRecord ::
    Monad m =>
    OrderT m (Sugar.Composite name (T m) o (Sugar.Expression name (T m) o (Sugar.Payload name i o a)))
orderRecord r =
    r
    & Sugar.cItems (orderByTag (^. Sugar.ciTag . Sugar.tagInfo))
    >>= traverse orderNode

instance Monad m => Order m name o (Sugar.LabeledApply name (T m) o)

orderCase ::
    Monad m =>
    OrderT m (Sugar.Case name (T m) o (Sugar.Expression name (T m) o (Sugar.Payload name i o a)))
orderCase = Sugar.cBody orderRecord

instance Monad m => Order m name o (Sugar.Lambda name (T m) o)
instance Monad m => Order m name o (Lens.Const a)
instance Monad m => Order m name o (Sugar.Else name (T m) o)
instance Monad m => Order m name o (Sugar.IfElse name (T m) o)
instance Monad m => Order m name o (Sugar.Let name (T m) o)
instance Monad m => Order m name o (Sugar.Function name (T m) o)
    -- The ordering for binder params already occurs at the Assignment's conversion,
    -- because it needs to be consistent with the presentation mode.

-- Special case assignment and binder to invoke the special cases in expr

instance Monad m => Order m name o (Sugar.AssignmentBody name (T m) o) where
    order (Sugar.BodyPlain x) = Sugar.apBody order x <&> Sugar.BodyPlain
    order (Sugar.BodyFunction x) = order x <&> Sugar.BodyFunction

instance Monad m => Order m name o (Sugar.Binder name (T m) o) where
    order (Sugar.BinderExpr x) = order x <&> Sugar.BinderExpr
    order (Sugar.BinderLet x) = order x <&> Sugar.BinderLet

instance Monad m => Order m name o (Sugar.Body name (T m) o) where
    order (Sugar.BodyLam l) = order l <&> Sugar.BodyLam
    order (Sugar.BodyRecord r) = orderRecord r <&> Sugar.BodyRecord
    order (Sugar.BodyLabeledApply a) = order a <&> Sugar.BodyLabeledApply
    order (Sugar.BodyCase c) = orderCase c <&> Sugar.BodyCase
    order (Sugar.BodyHole a) = SugarLens.holeTransformExprs orderNode a & Sugar.BodyHole & pure
    order (Sugar.BodyFragment a) =
        a
        & Sugar.fOptions . Lens.mapped . Lens.mapped %~ SugarLens.holeOptionTransformExprs orderNode
        & Sugar.BodyFragment
        & pure
    order (Sugar.BodyIfElse x) = order x <&> Sugar.BodyIfElse
    order (Sugar.BodyInject x) = (Sugar.iContent . Sugar._InjectVal) orderNode x <&> Sugar.BodyInject
    order (Sugar.BodyToNom x) = traverse orderNode x <&> Sugar.BodyToNom
    order (Sugar.BodyFromNom x) = traverse orderNode x <&> Sugar.BodyFromNom
    order (Sugar.BodySimpleApply x) = monoChildren orderNode x <&> Sugar.BodySimpleApply
    order (Sugar.BodyGetField x) = traverse orderNode x <&> Sugar.BodyGetField
    order x@Sugar.BodyLiteral{} = pure x
    order x@Sugar.BodyGetVar{} = pure x
    order x@Sugar.BodyPlaceHolder{} = pure x

orderNode ::
    (Monad m, Order m name o f) =>
    OrderT m (Node (Ann (Sugar.Payload name i o a)) f)
orderNode (Ann a x) =
    Ann
    <$> (Sugar.plAnnotation . SugarLens.annotationTypes) orderType a
    <*> order x

orderDef ::
    Monad m => OrderT m (Sugar.Definition name (T m) o (Sugar.Payload name i o a))
orderDef def =
    def
    & (SugarLens.defSchemes . Sugar.schemeType) orderType
    >>= (Sugar.drBody . Sugar._DefinitionBodyExpression . Sugar.deContent) orderNode

{-# INLINE orderedFlatComposite #-}
orderedFlatComposite ::
    Lens.Iso (T.Composite a) (T.Composite b)
    ([(T.Tag, T.Type)], Maybe (T.Var (T.Composite a)))
    ([(T.Tag, T.Type)], Maybe (T.Var (T.Composite b)))
orderedFlatComposite =
    Lens.iso to from
    where
        to T.CEmpty = ([], Nothing)
        to (T.CVar x) = ([], Just x)
        to (T.CExtend tag typ rest) = to rest & Lens._1 %~ (:) (tag, typ)
        from ([], Nothing) = T.CEmpty
        from ([], Just x) = T.CVar x
        from ((tag,typ):rest, v) = (rest, v) & from & T.CExtend tag typ

orderedClosedFlatComposite :: Lens.Prism' (T.Composite b) [(T.Tag, T.Type)]
orderedClosedFlatComposite = orderedFlatComposite . Lens.tagged Lens._Nothing
