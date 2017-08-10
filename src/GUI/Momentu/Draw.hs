{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
-- | Draw on elements

module GUI.Momentu.Draw
    ( addInnerFrame, backgroundColor
    ) where

import           Data.Vector.Vector2 (Vector2(..))
import           GUI.Momentu.Animation (R)
import qualified GUI.Momentu.Animation as Anim
import           GUI.Momentu.Element (Element)
import qualified GUI.Momentu.Element as Element
import qualified Graphics.DrawingCombinators as Draw

import           Lamdu.Prelude

backgroundColor ::
    (MonadReader env m, Element.HasAnimIdPrefix env, Element a) =>
    m (Draw.Color -> a -> a)
backgroundColor =
    Element.subAnimId ["bg"] <&>
    \animId color -> Element.setLayers %@~ \sz x ->
    x
    & Element.layers %~ addBg (Anim.backgroundColor animId color sz)
    where
        addBg bg [] = [bg]
        addBg bg (x:xs) = x <> bg : xs

addInnerFrame ::
    (MonadReader env m, Element.HasAnimIdPrefix env, Element a) =>
    m (Draw.Color -> Vector2 R -> a -> a)
addInnerFrame =
    Element.subAnimId ["inner-frame"] <&>
    \animId color frameWidth -> Element.bottomLayer %@~ \sz ->
    mappend
    ( Anim.emptyRectangle frameWidth sz animId
        & Anim.unitImages %~ Draw.tint color
    )