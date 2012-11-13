{-# LANGUAGE OverloadedStrings #-}
module Editor.CodeEdit (make) where

import Control.Lens ((^.))
import Control.Monad (liftM)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (StateT, mapStateT)
import Data.Cache (Cache)
import Data.List (intersperse)
import Data.List.Utils (enumerate, insertAt, removeAt)
import Data.Maybe (listToMaybe)
import Data.Monoid (Monoid(..))
import Data.Store.Guid (Guid)
import Data.Store.Transaction (Transaction)
import Editor.Anchors (ViewTag)
import Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad (WidgetT, ExprGuiM)
import Editor.CodeEdit.Settings (Settings)
import Editor.MonadF (MonadF)
import Editor.WidgetEnvT (WidgetEnvT)
import Graphics.UI.Bottle.Widget (Widget)
import qualified Control.Lens as Lens
import qualified Data.Store.IRef as IRef
import qualified Data.Store.Property as Property
import qualified Editor.Anchors as Anchors
import qualified Editor.BottleWidgets as BWidgets
import qualified Editor.CodeEdit.DefinitionEdit as DefinitionEdit
import qualified Editor.CodeEdit.ExpressionEdit as ExpressionEdit
import qualified Editor.CodeEdit.ExpressionEdit.ExpressionGui as ExpressionGui
import qualified Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad as ExprGuiM
import qualified Editor.CodeEdit.Sugar as Sugar
import qualified Editor.Config as Config
import qualified Editor.Layers as Layers
import qualified Editor.WidgetEnvT as WE
import qualified Editor.WidgetIds as WidgetIds
import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.Bottle.Animation as Anim
import qualified Graphics.UI.Bottle.Widget as Widget
import qualified Graphics.UI.Bottle.Widgets.Box as Box
import qualified Graphics.UI.Bottle.Widgets.FocusDelegator as FocusDelegator
import qualified Graphics.UI.Bottle.Widgets.Spacer as Spacer

type T = Transaction ViewTag

-- This is not in Sugar because Sugar is for code
data SugarPane m = SugarPane
  { spDef :: Sugar.Definition m
  , mDelPane :: Maybe (T m Guid)
  , mMovePaneDown :: Maybe (T m ())
  , mMovePaneUp :: Maybe (T m ())
  }

makeNewDefinitionAction :: Monad m => ExprGuiM m (T m Widget.Id)
makeNewDefinitionAction = do
  curCursor <- ExprGuiM.widgetEnv WE.readCursor
  return $ do
    newDefI <- Anchors.makeDefinition
    Anchors.newPane newDefI
    Anchors.savePreJumpPosition curCursor
    return . FocusDelegator.delegatingId $ WidgetIds.fromIRef newDefI

makeSugarPanes :: Monad m => StateT Cache (T m) [SugarPane m]
makeSugarPanes = do
  panes <- lift $ Anchors.getP Anchors.panes
  let
    mkMDelPane i
      | length panes >= 1 = Just $ do
        let newPanes = removeAt i panes
        Anchors.setP Anchors.panes newPanes
        return . maybe panesGuid IRef.guid . listToMaybe . reverse $
          take (i+1) newPanes
      | otherwise = Nothing
    movePane oldIndex newIndex = do
      let
        (before, item:after) = splitAt oldIndex panes
        newPanes = insertAt newIndex item $ before ++ after
      Anchors.setP Anchors.panes newPanes
    mkMMovePaneDown i
      | i+1 < length panes = Just $ movePane i (i+1)
      | otherwise = Nothing
    mkMMovePaneUp i
      | i-1 >= 0 = Just $ movePane i (i-1)
      | otherwise = Nothing
    convertPane (i, defI) = do
      sugarConfig <- lift $ liftM Property.value Anchors.sugarConfig
      sDef <- Sugar.loadConvertDefinition sugarConfig defI
      return SugarPane
        { spDef = sDef
        , mDelPane = mkMDelPane i
        , mMovePaneDown = mkMMovePaneDown i
        , mMovePaneUp = mkMMovePaneUp i
        }
  mapM convertPane $ enumerate panes

makeClipboardsEdit ::
  MonadF m => [Sugar.Expression m] -> ExprGuiM m (WidgetT m)
makeClipboardsEdit clipboards = do
  clipboardsEdits <-
    mapM (liftM (Lens.view ExpressionGui.egWidget) . ExpressionEdit.make) clipboards
  clipboardTitle <-
    if null clipboardsEdits
    then return Spacer.empty
    else ExprGuiM.widgetEnv $ BWidgets.makeTextView "Clipboards:" ["clipboards title"]
  return . Box.vboxAlign 0 $ clipboardTitle : clipboardsEdits

make ::
  MonadF m => Settings ->
  StateT Cache (WidgetEnvT (T m)) (Widget (T m))
make settings = do
  sugarPanes <- mapStateT lift makeSugarPanes
  clipboardsExprs <- mapStateT lift $ do
    clipboardsP <- lift Anchors.clipboards
    sugarConfig <- lift $ liftM Property.value Anchors.sugarConfig
    mapM (Sugar.loadConvertExpression sugarConfig) $
      Property.list clipboardsP
  ExprGuiM.run ExpressionEdit.make settings $ do
    panesEdit <- makePanesEdit sugarPanes
    clipboardsEdit <- makeClipboardsEdit clipboardsExprs
    return $
      Box.vboxAlign 0
      [ panesEdit
      , clipboardsEdit
      ]

panesGuid :: Guid
panesGuid = IRef.guid Anchors.panesIRef

makePanesEdit :: MonadF m => [SugarPane m] -> ExprGuiM m (WidgetT m)
makePanesEdit panes = do
  panesWidget <-
    case panes of
    [] -> ExprGuiM.widgetEnv $ BWidgets.makeFocusableTextView "<No panes>" myId
    (firstPane:_) ->
      (ExprGuiM.assignCursor myId . WidgetIds.fromGuid . Sugar.drGuid . spDef) firstPane $ do
        definitionEdits <- mapM makePaneWidget panes
        return . Box.vboxAlign 0 $ intersperse (Spacer.makeWidget 50) definitionEdits

  mJumpBack <- ExprGuiM.transaction Anchors.jumpBack
  newDefinition <- makeNewDefinitionAction
  let
    panesEventMap =
      mconcat
      [ Widget.keysEventMapMovesCursor Config.newDefinitionKeys
        "New definition" newDefinition
      , maybe mempty
        (Widget.keysEventMapMovesCursor Config.previousCursorKeys
         "Go to previous position") mJumpBack
      ]

  return $ Widget.weakerEvents panesEventMap panesWidget
  where
    myId = WidgetIds.fromGuid panesGuid
    paneEventMap pane = mconcat
      [ maybe mempty (Widget.keysEventMapMovesCursor Config.closePaneKeys "Close pane" . liftM WidgetIds.fromGuid) $ mDelPane pane
      , maybe mempty (Widget.keysEventMap Config.movePaneDownKeys "Move pane down") $ mMovePaneDown pane
      , maybe mempty (Widget.keysEventMap Config.movePaneUpKeys "Move pane up") $ mMovePaneUp pane
      ]
    onEachPane widget
      | widget ^. Widget.wIsFocused = onActivePane widget
      | otherwise = onInactivePane widget
    onActivePane =
      Widget.backgroundColor Layers.activePane WidgetIds.activeDefBackground Config.activeDefBGColor
    onInactivePane =
      (Lens.over Widget.wFrame . Anim.onImages . Draw.tint)
      Config.inactiveTintColor
    makePaneWidget pane =
      liftM (onEachPane . Widget.weakerEvents (paneEventMap pane)) .
      makeDefinitionEdit $ spDef pane
    makeDefinitionEdit = DefinitionEdit.make
