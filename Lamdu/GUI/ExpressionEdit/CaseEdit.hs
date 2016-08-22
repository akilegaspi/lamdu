{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
module Lamdu.GUI.ExpressionEdit.CaseEdit
    ( make
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Data.Maybe (fromMaybe)
import           Data.Monoid ((<>))
import           Data.Vector.Vector2 (Vector2(..))
import           Graphics.UI.Bottle.Animation (AnimId)
import qualified Graphics.UI.Bottle.Animation as Anim
import qualified Graphics.UI.Bottle.EventMap as E
import           Graphics.UI.Bottle.View (View(..))
import qualified Graphics.UI.Bottle.Widget as Widget
import           Graphics.UI.Bottle.Widget (Widget)
import qualified Graphics.UI.Bottle.Widgets.Layout as Layout
import           Lamdu.Calc.Type (Tag)
import qualified Lamdu.Calc.Val as V
import           Lamdu.Config (Config)
import qualified Lamdu.Config as Config
import qualified Lamdu.Eval.Results as ER
import qualified Lamdu.GUI.ExpressionEdit.EventMap as ExprEventMap
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

destCursorId ::
    [Sugar.CaseAlt name n (Sugar.Expression name n p)] ->
    Widget.Id -> Widget.Id
destCursorId [] defDestId = defDestId
destCursorId (alt : _) _ =
    alt ^. Sugar.caHandler . Sugar.rPayload & WidgetIds.fromExprPayload

make ::
    Monad m =>
    Sugar.Case (Name m) m (ExprGuiT.SugarExpr m) ->
    Sugar.Payload m ExprGuiT.Payload ->
    ExprGuiM m (ExpressionGui m)
make (Sugar.Case mArg alts caseTail addAlt cEntityId) pl =
    ExpressionGui.stdWrapParentExpr pl $ \myId ->
    let headerId = Widget.joinId myId ["header"]
    in ExprGuiM.assignCursor myId (destCursorId alts headerId) $
    do
        config <- ExprGuiM.readConfig
        let mExprAfterHeader =
                ( alts ^.. Lens.traversed . Lens.traversed
                ++ caseTail ^.. Lens.traversed
                ) ^? Lens.traversed
        labelJumpHoleEventMap <-
            mExprAfterHeader <&> ExprGuiT.nextHolesBefore
            & Lens._Just ExprEventMap.jumpHolesEventMap
            <&> fromMaybe mempty
        let headerLabel text =
                ExpressionGui.makeFocusableView headerId
                <*>
                (ExpressionGui.grammarLabel text
                    (Widget.toAnimId (WidgetIds.fromEntityId cEntityId))
                    <&> Widget.weakerEvents labelJumpHoleEventMap
                )
                <&> ExpressionGui.fromLayout
        (mActiveTag, header) <-
            case mArg of
            Sugar.LambdaCase -> headerLabel "λ:" <&> (,) Nothing
            Sugar.CaseWithArg (Sugar.CaseArg arg toLambdaCase) ->
                do
                    argEdit <-
                        ExprGuiM.makeSubexpression (const 0) arg
                        <&> ExpressionGui.egWidget %~ Widget.weakerEvents
                            (toLambdaCaseEventMap config toLambdaCase)
                    caseLabel <- headerLabel ":"
                    mTag <-
                        ExpressionGui.evaluationResult (arg ^. Sugar.rPayload)
                        <&> (>>= (^? ER.body . ER._RInject . V.injectTag))
                    return (mTag, ExpressionGui.combine [argEdit, caseLabel])
        (altsGui, resultPickers) <-
            ExprGuiM.listenResultPickers $
            do
                altsGui <- makeAltsWidget mActiveTag alts myId
                case caseTail of
                    Sugar.ClosedCase deleteTail ->
                        altsGui
                        & ExpressionGui.egWidget %~
                          Widget.weakerEvents
                          (caseOpenEventMap config deleteTail)
                        & return
                    Sugar.CaseExtending rest ->
                        altsGui
                        & makeOpenCase rest (Widget.toAnimId myId)
        let addAltEventMap =
                addAlt
                <&> (^. Sugar.caarNewTag . Sugar.tagInstance)
                <&> WidgetIds.fromEntityId
                <&> TagEdit.diveToCaseTag
                & Widget.keysEventMapMovesCursor (Config.caseAddAltKeys config)
                  (E.Doc ["Edit", "Case", "Add Alt"])
                & ExprGuiM.withHolePickers resultPickers
        ExpressionGui.addValFrame myId
            <*> (ExpressionGui.vboxTopFocalSpaced ??
                 ([header, altsGui] <&> ExpressionGui.egAlignment . _1 .~ 0))
            <&> ExpressionGui.egWidget %~ Widget.weakerEvents addAltEventMap

makeAltRow ::
    Monad m =>
    Maybe Tag ->
    Sugar.CaseAlt (Name m) m (Sugar.Expression (Name m) m ExprGuiT.Payload) ->
    ExprGuiM m (ExpressionGui m)
makeAltRow mActiveTag (Sugar.CaseAlt delete tag altExpr) =
    do
        config <- ExprGuiM.readConfig
        addBg <-
            ExpressionGui.addValBGWithColor Config.evaluatedPathBGColor
            (WidgetIds.fromEntityId (tag ^. Sugar.tagInstance))
        let mAddBg
                | mActiveTag == Just (tag ^. Sugar.tagVal) = addBg
                | otherwise = id
        altRefGui <-
            TagEdit.makeCaseTag (ExprGuiT.nextHolesBefore altExpr) tag
            <&> mAddBg
        altExprGui <- ExprGuiM.makeSubexpression (const 0) altExpr
        let itemEventMap = caseDelEventMap config delete
        ExpressionGui.tagItem ?? altRefGui ?? altExprGui
            <&> ExpressionGui.egWidget %~ Widget.weakerEvents itemEventMap

makeAltsWidget ::
    Monad m =>
    Maybe Tag ->
    [Sugar.CaseAlt (Name m) m (Sugar.Expression (Name m) m ExprGuiT.Payload)] ->
    Widget.Id -> ExprGuiM m (ExpressionGui m)
makeAltsWidget _ [] myId =
    ExpressionGui.makeFocusableView (Widget.joinId myId ["Ø"])
    <*> ExpressionGui.grammarLabel "Ø" (Widget.toAnimId myId)
    <&> ExpressionGui.fromLayout
makeAltsWidget mActiveTag alts _ =
    ExpressionGui.vboxTopFocalSpaced <*> mapM (makeAltRow mActiveTag) alts

separationBar :: Config -> Widget.R -> Anim.AnimId -> Widget a
separationBar config width animId =
    Anim.unitSquare (animId <> ["tailsep"])
    & View 1
    & Widget.fromView
    & Widget.tint (Config.caseTailColor config)
    & Widget.scale (Vector2 width 10)

makeOpenCase ::
    Monad m =>
    ExprGuiT.SugarExpr m -> AnimId -> ExpressionGui m ->
    ExprGuiM m (ExpressionGui m)
makeOpenCase rest animId altsGui =
    do
        config <- ExprGuiM.readConfig
        vspace <- ExpressionGui.stdVSpace
        restExpr <-
            ExpressionGui.addValPadding
            <*> ExprGuiM.makeSubexpression (const 0) rest
        return $ ExpressionGui $
            \layoutMode ->
            let restLayout = layoutMode & restExpr ^. ExpressionGui.egWidget
                alts = layoutMode & altsGui ^. ExpressionGui.egWidget
                sepBarWidth = min (restLayout ^. Widget.width) (alts ^. Widget.width)
            in
            alts
            & Layout.alignment . _1 .~ 0
            & Layout.addAfter Layout.Vertical
            ( [ separationBar config sepBarWidth animId & Layout.fromCenteredWidget
              , Layout.fromCenteredWidget vspace
              , restLayout
              ] <&> (Layout.alignment . _1 .~ 0)
            )

caseOpenEventMap ::
    Monad m =>
    Config -> m Sugar.EntityId -> Widget.EventMap (m Widget.EventResult)
caseOpenEventMap config open =
    Widget.keysEventMapMovesCursor (Config.caseOpenKeys config)
    (E.Doc ["Edit", "Case", "Open"]) $ WidgetIds.fromEntityId <$> open

caseDelEventMap ::
    Monad m =>
    Config -> m Sugar.EntityId -> Widget.EventMap (m Widget.EventResult)
caseDelEventMap config delete =
    Widget.keysEventMapMovesCursor (Config.delKeys config)
    (E.Doc ["Edit", "Case", "Delete Alt"]) $ WidgetIds.fromEntityId <$> delete

toLambdaCaseEventMap ::
    Monad m =>
    Config -> m Sugar.EntityId -> Widget.EventMap (m Widget.EventResult)
toLambdaCaseEventMap config toLamCase =
    Widget.keysEventMapMovesCursor (Config.delKeys config)
    (E.Doc ["Edit", "Case", "Turn to Lambda-Case"]) $
    WidgetIds.fromEntityId <$> toLamCase
