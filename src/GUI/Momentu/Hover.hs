{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, FlexibleContexts, RankNTypes, UndecidableInstances #-}
module GUI.Momentu.Hover
    ( Style(..), frameColor, framePadding, bgColor, bgPadding
    , Hover, hover, sequenceHover
    , backgroundColor
    , HasStyle(..)
    , AnchoredWidget, anchor
    , hoverInPlaceOf, hoverBesideOptions
    , Ordered(..), forward, backward
    , hoverBesideOptionsAxis
    , Orientation(..)
    , hoverBeside
    , emplaceAt
    ) where

import qualified Control.Lens as Lens
import           Data.Aeson.TH (deriveJSON)
import qualified Data.Aeson.Types as Aeson
import           Data.List.Extended (minimumOn)
import           Data.List.Lens (prefixed)
import           Data.Vector.Vector2 (Vector2(..))
import           GUI.Momentu.Align (Aligned(..), value)
import           GUI.Momentu.Direction (Orientation(..), Order(..))
import qualified GUI.Momentu.Draw as Draw
import           GUI.Momentu.Element (Element, SizedElement)
import qualified GUI.Momentu.Element as Element
import           GUI.Momentu.Glue (Glue(..), GluesTo)
import qualified GUI.Momentu.Glue as Glue
import           GUI.Momentu.Rect (Rect(..))
import           GUI.Momentu.State (Gui)
import qualified GUI.Momentu.State as State
import           GUI.Momentu.View (View)
import qualified GUI.Momentu.View as View
import           GUI.Momentu.Widget (Widget(..), R, StrollOrder(..))
import qualified GUI.Momentu.Widget as Widget

import           Lamdu.Prelude

data Style = Style
    { _frameColor :: Draw.Color
    , _framePadding :: Vector2 R
    , _bgColor :: Draw.Color
    , _bgPadding :: Vector2 R
    } deriving (Eq, Generic, Show)
deriveJSON Aeson.defaultOptions
    {Aeson.fieldLabelModifier = (^?! prefixed "_")}
    ''Style

Lens.makeLenses ''Style

class HasStyle env where style :: Lens' env Style
instance HasStyle Style where style = id

backgroundColor :: HasStyle env => Lens' env Draw.Color
backgroundColor = style . bgColor

data AnchoredWidget a = AnchoredWidget
    { _anchorPoint :: Vector2 R
    , _anchored :: Widget a
    } deriving Functor
Lens.makeLenses ''AnchoredWidget

newtype Hover a = Hover { _unHover :: a }
Lens.makeLenses ''Hover

instance Element a => Element (Hover a) where
    setLayers = unHover . Element.setLayers
    hoverLayers = unHover %~ Element.hoverLayers
    assymetricPad p0 p1 = unHover %~ Element.assymetricPad p0 p1
    scale r = unHover %~ Element.scale r
    empty = Hover Element.empty

instance SizedElement a => SizedElement (Hover a) where
    size = unHover . Element.size

instance Widget.HasWidget AnchoredWidget where widget = anchored

instance (Functor f, a ~ f State.Update) => Element (AnchoredWidget a) where
    setLayers = anchored . Element.setLayers
    hoverLayers = anchored %~ Element.hoverLayers
    empty = AnchoredWidget 0 Element.empty
    assymetricPad tl br (AnchoredWidget point w) =
        AnchoredWidget
        { _anchorPoint = point + tl
        , _anchored = Element.assymetricPad tl br w
        }
    scale ratio (AnchoredWidget point w) =
        AnchoredWidget
        { _anchorPoint = point * ratio
        , _anchored = Element.scale ratio w
        }

instance (Functor f, a ~ f State.Update) => SizedElement (AnchoredWidget a) where
    size = anchored . Element.size

instance (Functor f, a ~ f State.Update) => Glue (AnchoredWidget a) (Hover View) where
    type Glued (AnchoredWidget a) (Hover View) =
        Hover (AnchoredWidget a)
    glue o ow (Hover ov) =
        Glue.glueH f o ow ov & Hover
        where
            f w v = w & Element.setLayers <>~ v ^. View.vAnimLayers

instance (Functor f, a ~ f State.Update) => Glue (Hover View) (AnchoredWidget a) where
    type Glued (Hover View) (AnchoredWidget a) =
        Hover (AnchoredWidget a)
    glue o (Hover ov) =
        Glue.glueH f o ov <&> Hover
        where
            f v w = w & Element.setLayers <>~ v ^. View.vAnimLayers

instance (Applicative f, a ~ b, b ~ f State.Update) => Glue (AnchoredWidget a) (Hover (Widget b)) where
    type Glued (AnchoredWidget a) (Hover (Widget b)) =
        Hover (AnchoredWidget a)
    glue orientation ow0 (Hover ow1) =
        Glue.glueH f orientation ow0 ow1 & Hover
        where
            f (AnchoredWidget pos w0) w1 =
                Widget.glueStates orientation (StrollOrder Forward) w0 w1
                & AnchoredWidget pos

instance (Applicative f, a ~ b, b ~ f State.Update) => Glue (Hover (Widget a)) (AnchoredWidget b) where
    type Glued (Hover (Widget a)) (AnchoredWidget b) =
        Hover (AnchoredWidget a)
    glue orientation (Hover ow0) =
        Glue.glueH f orientation ow0 <&> Hover
        where
            f w0 (AnchoredWidget pos w1) =
                -- The hover is always logically "after" the
                -- lower-layer widgets, no matter if it is glued
                -- before/after geometrically
                AnchoredWidget pos (Widget.glueStates orientation (StrollOrder Backward) w0 w1)

data Ordered a = Ordered
    { _forward :: a
    , _backward :: a
    } deriving (Functor, Foldable, Traversable)
Lens.makeLenses ''Ordered

instance Applicative Ordered where
    pure = join Ordered
    Ordered fa fb <*> Ordered xa xb =
        Ordered (fa xa) (fb xb)

hoverBesideOptionsAxis ::
    ( Glue a b, Glue b a
    , SizedElement a, SizedElement b, SizedElement (Glued a b)
    ) =>
    Orientation -> Ordered a -> b -> [Glued a b]
hoverBesideOptionsAxis o (Ordered fwd bwd) src =
    do
        x <- [0, 1]
        let aSrc = Aligned x src
        [glue o aSrc (Aligned x fwd), glue o (Aligned x bwd) aSrc]
            <&> (^. value)

anchor :: Widget a -> AnchoredWidget a
anchor = AnchoredWidget 0

hoverBesideOptions ::
    ( Glue a b, Glue b a
    , SizedElement a, SizedElement b, SizedElement (Glued a b)
    ) =>
    a -> b -> [Glued a b]
hoverBesideOptions h src =
    do
        o <- [Vertical, Horizontal]
        hoverBesideOptionsAxis o (Ordered h h) src

addFrame ::
    (MonadReader env m, HasStyle env, SizedElement a, Element.HasAnimIdPrefix env) =>
    m (a -> a)
addFrame =
    do
        s <- Lens.view style
        animId <- Lens.view Element.animIdPrefix
        pure $ \gui ->
            if gui ^. Element.size == 0 then gui
            else
            gui
            & Element.pad (s ^. bgPadding)
            & Draw.backgroundColor (animId <> ["hover bg"]) (s ^. bgColor)
            & Element.pad (s ^. framePadding)
            & Draw.backgroundColor (animId <> ["hover frame"]) (s ^. frameColor)

hover ::
    (MonadReader env m, SizedElement a, HasStyle env, Element.HasAnimIdPrefix env) =>
    m (a -> Hover a)
hover = addFrame <&> ((Hover . Element.hoverLayers) .)

sequenceHover :: Functor f => Hover (f a) -> f (Hover a)
sequenceHover (Hover x) = x <&> Hover

emplaceAt ::
    Functor f =>
    Gui AnchoredWidget f ->
    Gui AnchoredWidget f ->
    Gui Widget f
emplaceAt h place =
    Element.assymetricPad translation 0 (h ^. anchored)
    & Element.size .~ place ^. Element.size
    where
        translation = place ^. anchorPoint - h ^. anchorPoint

-- TODO: Second argument here is really only (anchorPoint,size), take
-- it as such?
hoverInPlaceOf ::
    Functor f =>
    [Hover (Gui AnchoredWidget f)] ->
    Gui AnchoredWidget f -> Gui Widget f
hoverInPlaceOf [] _ = error "no hover options!"
hoverInPlaceOf hoverOptions@(Hover defaultOption:_) place
    | null focusedOptions =
        defaultOption `emplaceAt` place
    | otherwise =
        Widget
        { Widget._wSize = place ^. Element.size
        , Widget._wState = Widget.StateFocused makeFocused
        }
    where
        translation h = place ^. anchorPoint - h ^. anchorPoint
        -- All hovers *should* be same the - either focused or unfocused..
        focusedOptions =
            do
                Hover x <- hoverOptions
                mkFocused <- x ^.. anchored . Widget.wState . Widget._StateFocused
                pure (x, mkFocused)
        makeFocused surrounding =
            surrounding
            & Widget.sRight -~ sizeDiff ^. _1
            & Widget.sBottom -~ sizeDiff ^. _2
            & Widget.translateFocused (translation h) hMakeFocused
            & Widget.fFocalAreas %~ (Rect 0 (place ^. Element.size) :)
            where
                (h, hMakeFocused) = pickOption surrounding
                sizeDiff = h ^. Element.size - place ^. Element.size
        pickOption surrounding = minimumOn (negate . remainSurrouding surrounding . (^. _1)) focusedOptions
        remainSurrouding surrounding h =
            filter (>= 0)
            [ surrounding ^. Widget.sLeft - tl ^. _1
            , surrounding ^. Widget.sTop - tl ^. _2
            , surrounding ^. Widget.sRight - br ^. _1
            , surrounding ^. Widget.sBottom - br ^. _2
            ]
            & length
            where
                tl = negate (translation h)
                br = h ^. Element.size - place ^. Element.size - tl

hoverBeside ::
    ( GluesTo (Hover w) (Gui AnchoredWidget f) (Hover (Gui AnchoredWidget f))
    , SizedElement w
    , Element.HasAnimIdPrefix env, HasStyle env, MonadReader env m
    , Functor f
    ) =>
    (forall a b. Lens (t a) (t b) a b) ->
    m
    ( t (Gui Widget f) ->
      w -> t (Gui Widget f)
    )
hoverBeside lens =
    hover <&>
    \mkHover layout h ->
    let a = layout & lens %~ anchor
    in  a & lens %~
        hoverInPlaceOf
        (hoverBesideOptions (mkHover h) (a ^. lens))
