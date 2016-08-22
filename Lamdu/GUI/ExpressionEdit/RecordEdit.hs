{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
module Lamdu.GUI.ExpressionEdit.RecordEdit
    ( make
    ) where

import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Data.Monoid ((<>))
import           Data.Vector.Vector2 (Vector2(..))
import           Graphics.UI.Bottle.Animation (AnimId)
import qualified Graphics.UI.Bottle.Animation as Anim
import qualified Graphics.UI.Bottle.EventMap as E
import           Graphics.UI.Bottle.View (View(..))
import qualified Graphics.UI.Bottle.Widget as Widget
import           Graphics.UI.Bottle.Widget (Widget)
import qualified Graphics.UI.Bottle.Widgets.Layout as Layout
import           Lamdu.Config (Config)
import qualified Lamdu.Config as Config
import qualified Lamdu.GUI.ExpressionEdit.TagEdit as TagEdit
import           Lamdu.GUI.ExpressionGui (ExpressionGuiM(..), ExpressionGui)
import qualified Lamdu.GUI.ExpressionGui as ExpressionGui
import           Lamdu.GUI.ExpressionGui.Monad (ExprGuiM)
import qualified Lamdu.GUI.ExpressionGui.Monad as ExprGuiM
import qualified Lamdu.GUI.ExpressionGui.Types as ExprGuiT
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import           Lamdu.Sugar.Names.Types (Name(..))
import qualified Lamdu.Sugar.Types as Sugar

import           Prelude.Compat

defaultPos ::
    [Sugar.RecordField name m (Sugar.Expression name m a)] ->
    Widget.Id -> Widget.Id
defaultPos [] myId = myId
defaultPos (f : _) _ =
    f ^. Sugar.rfExpr . Sugar.rPayload & WidgetIds.fromExprPayload

shouldAddBg :: Monad m => Sugar.Record name m a -> Bool
shouldAddBg (Sugar.Record [] Sugar.ClosedRecord{} _) = False
shouldAddBg _ = True

make ::
    Monad m =>
    Sugar.Record (Name m) m (ExprGuiT.SugarExpr m) ->
    Sugar.Payload m ExprGuiT.Payload ->
    ExprGuiM m (ExpressionGui m)
make record@(Sugar.Record fields recordTail addField) pl =
    ExpressionGui.stdWrapParentExpr pl $ \myId ->
    ExprGuiM.assignCursor myId (defaultPos fields myId) $
    do
        config <- ExprGuiM.readConfig
        (gui, resultPickers) <-
            ExprGuiM.listenResultPickers $
            do
                fieldsGui <-
                    (if addBg then ExpressionGui.addValPadding else return id)
                    <*>  makeFieldsWidget fields myId
                case recordTail of
                    Sugar.ClosedRecord deleteTail ->
                        fieldsGui
                        & ExpressionGui.egWidget %~
                          Widget.weakerEvents (recordOpenEventMap config deleteTail)
                        & return
                    Sugar.RecordExtending rest ->
                        makeOpenRecord fieldsGui rest (Widget.toAnimId myId)
        let addFieldEventMap =
                addField
                <&> (^. Sugar.rafrNewTag . Sugar.tagInstance)
                <&> WidgetIds.fromEntityId
                <&> TagEdit.diveToRecordTag
                & Widget.keysEventMapMovesCursor (Config.recordAddFieldKeys config)
                  (E.Doc ["Edit", "Record", "Add Field"])
                & ExprGuiM.withHolePickers resultPickers
        gui
            & ExpressionGui.egWidget %~ Widget.weakerEvents addFieldEventMap
            & if addBg
                then
                    (<*>)
                    (ExpressionGui.addValBG myId <&> (ExpressionGui.egWidget %~))
                    . return
                else return
    where
        addBg = shouldAddBg record

makeFieldRow ::
    Monad m =>
    Sugar.RecordField (Name m) m (Sugar.Expression (Name m) m ExprGuiT.Payload) ->
    ExprGuiM m (ExpressionGui m)
makeFieldRow (Sugar.RecordField delete tag fieldExpr) =
    do
        config <- ExprGuiM.readConfig
        fieldRefGui <-
            TagEdit.makeRecordTag (ExprGuiT.nextHolesBefore fieldExpr) tag
        fieldExprGui <- ExprGuiM.makeSubexpression (const 0) fieldExpr
        let itemEventMap = recordDelEventMap config delete
        ExpressionGui.tagItem ?? fieldRefGui ?? fieldExprGui
            <&> ExpressionGui.egWidget %~ Widget.weakerEvents itemEventMap

makeFieldsWidget ::
    Monad m =>
    [Sugar.RecordField (Name m) m (Sugar.Expression (Name m) m ExprGuiT.Payload)] ->
    Widget.Id -> ExprGuiM m (ExpressionGui m)
makeFieldsWidget [] myId =
    ExpressionGui.makeFocusableView myId
    <*> ExpressionGui.grammarLabel "()" (Widget.toAnimId myId)
    <&> ExpressionGui.fromLayout
makeFieldsWidget fields _ =
    ExpressionGui.vboxTopFocalSpaced <*> mapM makeFieldRow fields

separationBar :: Config -> Widget.R -> Anim.AnimId -> Widget a
separationBar config width animId =
    Anim.unitSquare (animId <> ["tailsep"])
    & View 1
    & Widget.fromView
    & Widget.tint (Config.recordTailColor config)
    & Widget.scale (Vector2 width 10)

makeOpenRecord ::
    Monad m =>
    ExpressionGui m -> ExprGuiT.SugarExpr m -> AnimId ->
    ExprGuiM m (ExpressionGui m)
makeOpenRecord fieldsGui rest animId =
    do
        config <- ExprGuiM.readConfig
        vspace <- ExpressionGui.stdVSpace
        restExpr <-
            ExpressionGui.addValPadding
            <*> ExprGuiM.makeSubexpression (const 0) rest
        return $ ExpressionGui $
            \layoutMode ->
            let restLayout = layoutMode & restExpr ^. ExpressionGui.egWidget
                minWidth = restLayout ^. Widget.width
                fields = layoutMode & fieldsGui ^. ExpressionGui.egWidget
                targetWidth = fields ^. Widget.width
            in
            fields
            & Layout.alignment . _1 .~ 0
            & Layout.addAfter Layout.Vertical
            ( [ separationBar config (max minWidth targetWidth) animId
                & Layout.fromCenteredWidget
              , Layout.fromCenteredWidget vspace
              , restLayout
              ] <&> Layout.alignment . _1 .~ 0
            )

recordOpenEventMap ::
    Monad m =>
    Config -> m Sugar.EntityId -> Widget.EventMap (m Widget.EventResult)
recordOpenEventMap config open =
    Widget.keysEventMapMovesCursor (Config.recordOpenKeys config)
    (E.Doc ["Edit", "Record", "Open"]) $ WidgetIds.fromEntityId <$> open

recordDelEventMap ::
    Monad m =>
    Config -> m Sugar.EntityId -> Widget.EventMap (m Widget.EventResult)
recordDelEventMap config delete =
    Widget.keysEventMapMovesCursor (Config.delKeys config)
    (E.Doc ["Edit", "Record", "Delete Field"]) $ WidgetIds.fromEntityId <$> delete
