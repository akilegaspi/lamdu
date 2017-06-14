{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
module Lamdu.GUI.DefinitionEdit
    ( make
    ) where

import qualified Control.Lens as Lens
import qualified Control.Monad.Reader as Reader
import           Control.Monad.Transaction (transaction)
import qualified Data.List as List
import qualified Data.Store.Property as Property
import           Data.Store.Transaction (Transaction)
import qualified Data.Store.Transaction as Transaction
import           Data.Vector.Vector2 (Vector2(..))
import qualified Graphics.DrawingCombinators as Draw
import           Graphics.UI.Bottle.Animation (AnimId)
import qualified Graphics.UI.Bottle.Animation as Anim
import qualified Graphics.UI.Bottle.EventMap as E
import           Graphics.UI.Bottle.MetaKey (MetaKey(..), noMods)
import           Graphics.UI.Bottle.View (View(..))
import qualified Graphics.UI.Bottle.View as View
import           Graphics.UI.Bottle.Widget (Widget)
import qualified Graphics.UI.Bottle.Widget as Widget
import qualified Graphics.UI.Bottle.Widget.Aligned as AlignedWidget
import qualified Graphics.UI.Bottle.Widgets.Box as Box
import qualified Graphics.UI.Bottle.Widgets.TextView as TextView
import qualified Graphics.UI.GLFW as GLFW
import           Lamdu.Calc.Type.Scheme (Scheme(..), schemeType)
import qualified Lamdu.Config.Theme as Theme
import qualified Lamdu.GUI.ExpressionEdit.BinderEdit as BinderEdit
import qualified Lamdu.GUI.ExpressionEdit.BuiltinEdit as BuiltinEdit
import qualified Lamdu.GUI.ExpressionGui as ExpressionGui
import           Lamdu.GUI.ExpressionGui.Monad (ExprGuiM)
import qualified Lamdu.GUI.ExpressionGui.Monad as ExprGuiM
import qualified Lamdu.GUI.ExpressionGui.Types as ExprGuiT
import qualified Lamdu.GUI.Spacing as Spacing
import qualified Lamdu.GUI.TypeView as TypeView
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import           Lamdu.Sugar.Names.Types (Name(..), DefinitionN)
import qualified Lamdu.Sugar.Types as Sugar

import           Lamdu.Prelude

type T = Transaction

addUndeleteButton ::
    Monad m =>
    T m Widget.Id ->
    (Widget.R -> Widget (T m Widget.EventResult)) ->
    ExprGuiM m (Widget.R -> Widget (T m Widget.EventResult))
addUndeleteButton undelete mkWidget =
    TextView.makeFocusableLabel "Undelete..."
    <&> E.weakerEvents eventMap
    <&> \undelButton width -> Box.vboxAlign 0 [mkWidget width, undelButton]
    where
        eventMap =
            Widget.keysEventMapMovesCursor [MetaKey noMods GLFW.Key'Enter]
            (E.Doc ["Edit", "Undelete definition"]) undelete

make ::
    Monad m =>
    DefinitionN m ExprGuiT.Payload ->
    ExprGuiM m (Widget.R -> Widget (T m Widget.EventResult))
make def =
    do
        defStateProp <-
            def ^. Sugar.drDefinitionState . Transaction.mkProperty
            & transaction
        let defState = Property.value defStateProp
        addDeletionDiagonal <-
            case defState of
            Sugar.DeletedDefinition -> ExpressionGui.addDeletionDiagonal ?? 0.02
            Sugar.LiveDefinition -> return id
        let mUndelete =
                case defState of
                Sugar.LiveDefinition -> Nothing
                Sugar.DeletedDefinition ->
                    myId <$ Property.set defStateProp Sugar.LiveDefinition & Just
        case def ^. Sugar.drBody of
            Sugar.DefinitionBodyExpression bodyExpr ->
                makeExprDefinition def bodyExpr
            Sugar.DefinitionBodyBuiltin builtin ->
                makeBuiltinDefinition def builtin <&> const
            <&> Lens.mapped %~ addDeletionDiagonal
            >>= maybe return addUndeleteButton mUndelete
    & Reader.local (View.animIdPrefix .~ Widget.toAnimId myId)
    where
        myId = def ^. Sugar.drEntityId & WidgetIds.fromEntityId

expandTo :: Widget.R -> Widget a -> Widget a
expandTo width eg
    | padding <= 0 = eg
    | otherwise = View.pad (Vector2 (padding / 2) 0) eg
    where
        padding = width - eg ^. View.width

topLevelSchemeTypeView ::
    Monad m =>
    Scheme -> Sugar.EntityId -> AnimId ->
    ExprGuiM m (Widget.R -> Widget a)
topLevelSchemeTypeView scheme entityId suffix =
    -- At the definition-level, Schemes can be shown as ordinary
    -- types to avoid confusing forall's:
    WidgetIds.fromEntityId entityId
    & (`Widget.joinId` suffix)
    & Widget.toAnimId
    & TypeView.make (scheme ^. schemeType)
    <&> Widget.fromView
    <&> flip expandTo

makeBuiltinDefinition ::
    Monad m =>
    Sugar.Definition (Name m) m (ExprGuiT.SugarExpr m) ->
    Sugar.DefinitionBuiltin m -> ExprGuiM m (Widget (T m Widget.EventResult))
makeBuiltinDefinition def builtin =
    do
        defColor <- ExprGuiM.readTheme <&> Theme.name <&> Theme.definitionColor
        assignment <-
            [ ExpressionGui.makeNameOriginEdit name defColor (Widget.joinId myId ["name"])
            , TextView.makeLabel "=" <&> Widget.fromView
            , BuiltinEdit.make builtin myId
            ]
            & sequenceA
            >>= Spacing.hboxCenteredSpaced
        let width = assignment ^. View.width
        typeView <-
            topLevelSchemeTypeView (builtin ^. Sugar.biType) entityId ["builtinType"]
            ?? width
        Box.vboxAlign 0 [assignment, typeView] & return
    where
        name = def ^. Sugar.drName
        entityId = def ^. Sugar.drEntityId
        myId = WidgetIds.fromEntityId entityId

typeIndicatorId :: Widget.Id -> Widget.Id
typeIndicatorId myId = Widget.joinId myId ["type indicator"]

typeIndicator ::
    Monad m => Draw.Color -> Widget.Id -> ExprGuiM m (Widget.R -> View)
typeIndicator color myId =
    ExprGuiM.readTheme
    <&>
    \theme width ->
    Anim.unitSquare (Widget.toAnimId (typeIndicatorId myId))
    & View.make 1
    & View.scale (Vector2 width (realToFrac (Theme.typeIndicatorFrameWidth theme ^. _2)))
    & View.tint color

makeExprDefinition ::
    Monad m =>
    Sugar.Definition (Name m) m (ExprGuiT.SugarExpr m) ->
    Sugar.DefinitionExpression (Name m) m (ExprGuiT.SugarExpr m) ->
    ExprGuiM m (Widget.R -> Widget (T m Widget.EventResult))
makeExprDefinition def bodyExpr =
    do
        theme <- ExprGuiM.readTheme
        let defColor = Theme.definitionColor (Theme.name theme)
        bodyGui <-
            BinderEdit.make (def ^. Sugar.drName) defColor
            (bodyExpr ^. Sugar.deContent) myId
        vspace <- ExpressionGui.stdVSpace
        mkTypeWidgets <-
            [ typeIndicator (Theme.typeIndicatorMatchColor theme) myId
                <&> fmap Widget.fromView
            , topLevelSchemeTypeView (bodyExpr ^. Sugar.deType) entityId
                ["exportedType"]
            ] & sequence <&> sequence
        return $ \width ->
            let bodyWidget = ExpressionGui.render width bodyGui ^. AlignedWidget.aWidget
            in
            bodyWidget : mkTypeWidgets (bodyWidget ^. View.width)
            & List.intersperse vspace
            & Box.vboxAlign 0
    where
        entityId = def ^. Sugar.drEntityId
        myId = WidgetIds.fromEntityId entityId
