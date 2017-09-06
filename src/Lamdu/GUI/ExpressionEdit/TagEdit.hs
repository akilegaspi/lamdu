{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
module Lamdu.GUI.ExpressionEdit.TagEdit
    ( makeRecordTag, makeCaseTag
    , makeParamTag
    , diveToRecordTag, diveToCaseTag
    ) where

import qualified Control.Lens as Lens
import qualified Control.Monad.Reader as Reader
import           Data.Store.Transaction (Transaction)
import           GUI.Momentu.Align (WithTextPos)
import qualified GUI.Momentu.Align as Align
import qualified GUI.Momentu.Draw as Draw
import qualified GUI.Momentu.EventMap as E
import qualified GUI.Momentu.Hover as Hover
import           GUI.Momentu.View (View)
import           GUI.Momentu.Widget (Widget)
import qualified GUI.Momentu.Widget as Widget
import qualified GUI.Momentu.Widgets.TextView as TextView
import qualified Lamdu.Config as Config
import qualified Lamdu.Config.Theme as Theme
import qualified Lamdu.GUI.ExpressionEdit.EventMap as ExprEventMap
import qualified Lamdu.GUI.ExpressionGui as ExpressionGui
import           Lamdu.GUI.ExpressionGui.Monad (ExprGuiM)
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import           Lamdu.Sugar.Names.Types (Name(..))
import           Lamdu.Sugar.NearestHoles (NearestHoles)
import qualified Lamdu.Sugar.NearestHoles as NearestHoles
import qualified Lamdu.Sugar.Types as Sugar

import           Lamdu.Prelude

type T = Transaction

makeTagNameEdit ::
    Monad m =>
    NearestHoles -> Widget.Id ->
    Sugar.Tag (Name m) m -> ExprGuiM m (WithTextPos (Widget (T m Widget.EventResult)))
makeTagNameEdit nearestHoles myId tag =
    do
        config <- Lens.view Config.config <&> Config.hole
        let keys = Config.holePickAndMoveToNextHoleKeys config
            jumpNextEventMap =
                nearestHoles ^. NearestHoles.next
                & maybe mempty
                  (Widget.keysEventMapMovesCursor keys
                   (E.Doc ["Navigation", "Jump to next hole"]) .
                   return . WidgetIds.fromEntityId)
        ExpressionGui.makeNameEdit
            (tag ^. Sugar.tagName) myId
            <&> Align.tValue . E.eventMap %~ E.filterChars (/= ',')
            <&> Align.tValue %~ E.weakerEvents jumpNextEventMap

makeTagEdit ::
    Monad m =>
    Draw.Color -> NearestHoles -> Sugar.Tag (Name m) m ->
    ExprGuiM m (WithTextPos (Widget (T m Widget.EventResult)))
makeTagEdit tagColor nearestHoles tag =
    do
        jumpHolesEventMap <- ExprEventMap.jumpHolesEventMap nearestHoles
        isRenaming <- Widget.isSubCursor ?? renameId
        config <- Lens.view Config.config
        let startRenaming =
                Widget.keysEventMapMovesCursor (Config.jumpToDefinitionKeys config)
                (E.Doc ["Edit", "Tag", "Open"]) (pure renameId)
        nameView <-
            (Widget.makeFocusableView ?? viewId <&> fmap) <*>
            ExpressionGui.makeNameView (tag ^. Sugar.tagName) (Widget.toAnimId myId)
            <&> Lens.mapped %~ E.weakerEvents startRenaming
        widget <-
            if isRenaming
            then ( Hover.hoverBeside Align.tValue ?? nameView )
                 <*>
                 ( makeTagNameEdit nearestHoles renameId tag <&> (^. Align.tValue) )
            else pure nameView
        widget
            <&> E.weakerEvents jumpHolesEventMap
            & pure
    & Reader.local (TextView.color .~ tagColor)
    & Widget.assignCursor myId viewId
    where
        myId = WidgetIds.fromEntityId (tag ^. Sugar.tagInfo . Sugar.tagInstance)
        renameId = myId `Widget.joinId` ["rename"]
        viewId = myId `Widget.joinId` ["view"]

makeRecordTag ::
    Monad m => NearestHoles -> Sugar.Tag (Name m) m ->
    ExprGuiM m (WithTextPos (Widget (T m Widget.EventResult)))
makeRecordTag nearestHoles tag =
    do
        theme <- Lens.view Theme.theme <&> Theme.name
        makeTagEdit (Theme.recordTagColor theme) nearestHoles tag

makeCaseTag ::
    Monad m => NearestHoles -> Sugar.Tag (Name m) m ->
    ExprGuiM m (WithTextPos (Widget (T m Widget.EventResult)))
makeCaseTag nearestHoles tag =
    do
        theme <- Lens.view Theme.theme <&> Theme.name
        makeTagEdit (Theme.caseTagColor theme) nearestHoles tag

-- | Unfocusable tag view (e.g: in apply params)
makeParamTag :: Monad m => Name m -> Sugar.EntityId -> ExprGuiM m (WithTextPos View)
makeParamTag name entityId =
    do
        theme <- Lens.view Theme.theme <&> Theme.name
        ExpressionGui.makeNameView name animId
            & Reader.local (TextView.color .~ Theme.paramTagColor theme)
    where
        animId = WidgetIds.fromEntityId entityId & Widget.toAnimId

diveToRecordTag :: Widget.Id -> Widget.Id
diveToRecordTag = WidgetIds.nameEditOf

diveToCaseTag :: Widget.Id -> Widget.Id
diveToCaseTag = WidgetIds.nameEditOf
