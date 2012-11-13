{-# LANGUAGE OverloadedStrings #-}

module Editor.CodeEdit.ExpressionEdit.ExpressionGui
  ( ExpressionGui(..), egWidget, atEgWidgetM
  , fromValueWidget
  , hbox, hboxSpaced, addBelow
  , addType -- TODO: s/type/info
  , TypeStyle(..)
  , parenify, wrapExpression, wrapParenify
  -- ExprGuiM:
  , wrapDelegated
  , makeNameEdit
  , nameSrcTint
  ) where

import Control.Lens ((^.))
import Control.Monad (liftM)
import Data.Function (on)
import Data.Store.Guid (Guid)
import Data.Store.Transaction (Transaction)
import Data.Vector.Vector2 (Vector2(..))
import Editor.Anchors (ViewTag)
import Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad (ExprGuiM)
import Editor.CodeEdit.ExpressionEdit.ExpressionGui.Types (WidgetT, ExpressionGui(..), egWidget, egAlignment)
import Editor.MonadF (MonadF)
import Graphics.UI.Bottle.Widget (Widget)
import Graphics.UI.Bottle.Widgets.Box (KBox)
import qualified Control.Lens as Lens
import qualified Data.List as List
import qualified Data.Vector.Vector2 as Vector2
import qualified Editor.Anchors as Anchors
import qualified Editor.BottleWidgets as BWidgets
import qualified Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad as ExprGuiM
import qualified Editor.CodeEdit.Sugar as Sugar
import qualified Editor.Config as Config
import qualified Editor.Layers as Layers
import qualified Editor.WidgetEnvT as WE
import qualified Editor.WidgetIds as WidgetIds
import qualified Graphics.UI.Bottle.EventMap as EventMap
import qualified Graphics.UI.Bottle.Widget as Widget
import qualified Graphics.UI.Bottle.Widgets.Box as Box
import qualified Graphics.UI.Bottle.Widgets.FocusDelegator as FocusDelegator
import qualified Graphics.UI.Bottle.Widgets.Grid as Grid
import qualified Graphics.UI.Bottle.Widgets.Spacer as Spacer
import qualified Graphics.UI.Bottle.Widgets.TextEdit as TextEdit

-- TODO: Which lens combinator to use instead?
atEgWidgetM ::
  Monad m =>
  (WidgetT f -> m (WidgetT f)) ->
  ExpressionGui f -> m (ExpressionGui f)
atEgWidgetM conv (ExpressionGui w a) =
  liftM (`ExpressionGui` a) $ conv w

fromValueWidget :: WidgetT m -> ExpressionGui m
fromValueWidget widget = ExpressionGui widget 0.5

hbox :: [ExpressionGui m] -> ExpressionGui m
hbox guis =
  ExpressionGui (Box.toWidget box) $
  case box ^. Box.boxContent of
  ((_, x) : _) -> x ^. Grid.elementAlign . Vector2.second
  _ -> error "hbox must not get empty list :("
  where
    box = Box.make Box.horizontal $ map f guis
    f (ExpressionGui widget alignment) = (Vector2 0.5 alignment, widget)

hboxSpaced :: [ExpressionGui m] -> ExpressionGui m
hboxSpaced = hbox . List.intersperse (fromValueWidget BWidgets.stdSpaceWidget)

fromBox :: KBox Bool (Transaction ViewTag m) -> ExpressionGui m
fromBox box =
  ExpressionGui (Box.toWidget box) alignment
  where
    alignment =
      maybe (error "True disappeared from box list?!")
        (Lens.view (Grid.elementAlign . Vector2.second)) .
      lookup True $ box ^. Box.boxContent

addBelow ::
  [(Box.Alignment, WidgetT m)] ->
  ExpressionGui m ->
  ExpressionGui m
addBelow ws eg =
  fromBox . Box.makeKeyed Box.vertical $
  (True, (Vector2 0.5 (eg ^. egAlignment), eg ^. egWidget)) :
  map ((,) False) ws

data TypeStyle = HorizLine | Background

wWidth :: Lens.SimpleLens (Widget f) Widget.R
wWidth = Widget.wSize . Vector2.first

addType ::
  TypeStyle ->
  Widget.Id ->
  [WidgetT m] ->
  ExpressionGui m ->
  ExpressionGui m
addType _ _ [] eg = eg
addType style exprId typeEdits eg =
  addBelow items eg
  where
    items = middleElement : [(0.5, annotatedTypes)]
    middleElement =
      case style of
      HorizLine -> (0.5, Spacer.makeHorizLine underlineId (Vector2 width 1))
      Background -> (0.5, Spacer.makeWidget 5)
    annotatedTypes =
      addBackground . Lens.set wWidth width $
      Widget.translate (Vector2 ((width - typesBox ^. wWidth)/2) 0) typesBox
    width = on max (Lens.view wWidth) (eg ^. egWidget) typesBox
    typesBox = Box.vboxCentered typeEdits
    isError = length typeEdits >= 2
    bgAnimId = Widget.toAnimId exprId ++ ["type background"]
    addBackground = maybe id (Widget.backgroundColor Layers.types bgAnimId) bgColor
    bgColor
      | isError = Just Config.inferredTypeErrorBGColor
      | otherwise = do
        Background <- Just style
        return Config.inferredTypeBGColor
    underlineId = WidgetIds.underlineId $ Widget.toAnimId exprId

exprFocusDelegatorConfig :: FocusDelegator.Config
exprFocusDelegatorConfig = FocusDelegator.Config
  { FocusDelegator.startDelegatingKey = Config.enterSubexpressionKey
  , FocusDelegator.startDelegatingDoc = "Enter subexpression"
  , FocusDelegator.stopDelegatingKey = Config.leaveSubexpressionKey
  , FocusDelegator.stopDelegatingDoc = "Leave subexpression"
  }

-- ExprGuiM GUIs (TODO: Move to Monad.hs?)

wrapDelegated ::
  (MonadF f, Monad m) =>
  FocusDelegator.Config -> FocusDelegator.IsDelegating ->
  ((Widget f -> Widget f) -> a -> b) ->
  (Widget.Id -> ExprGuiM m a) ->
  Widget.Id -> ExprGuiM m b
wrapDelegated =
  BWidgets.wrapDelegatedWith (ExprGuiM.widgetEnv WE.readCursor)
  (ExprGuiM.atEnv . WE.atEnvCursor)

makeNameEdit ::
  Monad m => (ExprGuiM.NameSource, String) -> Guid -> Widget.Id -> ExprGuiM m (WidgetT m)
makeNameEdit (nameSrc, name) ident myId =
  liftM (nameSrcTint nameSrc) .
  (ExprGuiM.atEnv . WE.atEnvTextStyle)
  ((Lens.set TextEdit.sEmptyUnfocusedString) name .
   (Lens.set TextEdit.sEmptyFocusedString) (concat ["<", name, ">"])) $
  ExprGuiM.widgetEnv . flip makeEditor myId =<<
  (ExprGuiM.transaction . Anchors.assocNameRef) ident
  where
    makeEditor =
      (fmap . fmap . liftM . Lens.over Widget.wEventMap)
      (EventMap.filterChars (`notElem` "[]\\`"))
      BWidgets.makeWordEdit

nameSrcTint :: ExprGuiM.NameSource -> Widget f -> Widget f
nameSrcTint ExprGuiM.AutoGeneratedName = Widget.tint Config.autoGeneratedNameTint
nameSrcTint ExprGuiM.StoredName = id

wrapExpression ::
  (Monad m, MonadF f) =>
  (Widget.Id -> ExprGuiM m (ExpressionGui f)) ->
  Widget.Id -> ExprGuiM m (ExpressionGui f)
wrapExpression =
  wrapDelegated exprFocusDelegatorConfig FocusDelegator.Delegating $ Lens.over egWidget

parenify ::
  Monad m =>
  Sugar.HasParens ->
  (Widget.Id -> ExpressionGui f -> ExprGuiM m (ExpressionGui f)) ->
  (Widget.Id -> ExprGuiM m (ExpressionGui f)) ->
  Widget.Id -> ExprGuiM m (ExpressionGui f)
parenify Sugar.DontHaveParens _ mkWidget myId = mkWidget myId
parenify Sugar.HaveParens addParens mkWidget myId = addParens myId =<< mkWidget myId

wrapParenify ::
  (MonadF f, Monad m) =>
  Sugar.HasParens ->
  (Widget.Id -> ExpressionGui f -> ExprGuiM m (ExpressionGui f)) ->
  (Widget.Id -> ExprGuiM m (ExpressionGui f)) ->
  Widget.Id -> ExprGuiM m (ExpressionGui f)
wrapParenify hasParens addParens =
  wrapExpression . parenify hasParens addParens
