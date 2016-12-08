{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}

module Graphics.UI.Bottle.Animation
    ( R, Size
    , Image(..), iAnimId, iUnitImage, iRect
    , Frame(..), frameImagesMap, unitImages
    , draw
    , initialState, nextState, currentFrame
    , mapIdentities
    , unitSquare, emptyRectangle
    , backgroundColor
    , translate, scale
    , unitIntoRect
    , simpleFrame, sizedFrame
    , State, stateMapIdentities, stateClearImages
    , module Graphics.UI.Bottle.Animation.Id
    ) where

import           Control.Applicative (liftA2)
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (void)
import qualified Data.List as List
import           Data.List.Utils (groupOn)
import           Data.Map (Map, (!))
import qualified Data.Map.Strict as Map
import           Data.Maybe (mapMaybe)
import           Data.Vector.Vector2 (Vector2(..))
import qualified Data.Vector.Vector2 as Vector2
import           GHC.Generics (Generic)
import           Graphics.DrawingCombinators (R, (%%))
import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.DrawingCombinators.Utils as DrawUtils
import           Graphics.UI.Bottle.Animation.Id
import           Graphics.UI.Bottle.Rect (Rect(Rect))
import qualified Graphics.UI.Bottle.Rect as Rect

import           Prelude.Compat

type Size = Vector2 R

data Image = Image
    { _iAnimId :: AnimId
    , _iUnitImage :: !(Draw.Image ())
        -- iUnitImage always occupies (0,0)..(1,1),
        -- the translation/scaling occurs when drawing
    , _iRect :: !Rect
    } deriving (Generic)
Lens.makeLenses ''Image

newtype Frame = Frame
    { _frameImagesMap :: Map AnimId [Image]
    } deriving (Generic)
Lens.makeLenses ''Frame

data Interpolation
    = Deleting Image
      -- ^ An image that is interpolating from its current state to nothingness
    | Modifying {-cur-}Image {-dest-}Rect
      -- ^ An image that is interpolating from the cur Rect towards the dest Image
    | Final Image
      -- ^ An image that finished interpolating
Lens.makePrisms ''Interpolation

interpolationImage :: Lens' Interpolation Image
interpolationImage f (Deleting img) = f img <&> Deleting
interpolationImage f (Modifying curImg destRect) = f curImg <&> (`Modifying` destRect)
interpolationImage f (Final img) = f img <&> Final

newtype State = State
    { _stateInterpolations :: [Interpolation]
    }
Lens.makeLenses ''State

currentFrame :: State -> Frame
currentFrame (State interpolations) =
    interpolations ^.. traverse . interpolationImage
    <&> f & Map.fromList & Frame
    where
        f img = (img ^. iAnimId, [img])

initialState :: State
initialState = State []

rectDistance :: Rect -> Rect -> R
rectDistance ra rb =
    liftA2 max
    (abs (ra ^. Rect.topLeft - rb ^. Rect.topLeft))
    (abs (ra ^. Rect.bottomRight - rb ^. Rect.bottomRight))
    & Vector2.uncurry max

advanceInterpolation :: R -> Interpolation -> Maybe Interpolation
advanceInterpolation _ x@Final{} = Just x
advanceInterpolation movement (Modifying curImage destRect)
    | rectDistance (curImage ^. iRect) destRect < equalityThreshold =
        curImage & iRect .~ destRect & Final & Just
    | otherwise =
        curImage
        & iRect .~
            Rect
            (animSpeed * destTopLeft + (1 - animSpeed) * curTopLeft)
            (animSpeed * destSize    + (1 - animSpeed) * curSize   )
        & (`Modifying` destRect) & Just
    where
        equalityThreshold = 0.2
        animSpeed = pure movement
        Rect destTopLeft destSize = destRect
        Rect curTopLeft curSize = curImage ^. iRect
advanceInterpolation movement (Deleting img)
    | Vector2.sqrNorm (img ^. iRect . Rect.size) < 1 = Nothing
    | otherwise =
        img
        & iRect . Rect.centeredSize *~ pure (1 - movement)
        & Deleting & Just

advanceState :: R -> State -> State
advanceState speed = stateInterpolations %~ mapMaybe (advanceInterpolation speed)

markDuplicates :: [Image] -> Image
markDuplicates (x:_:_) = x & iUnitImage %~ mappend (Draw.tint red unitX)
markDuplicates x = head x

setNewDest :: Frame -> State -> State
setNewDest destFrame state =
    concat
    [ Map.difference dest cur & Map.toList <&> add
    , Map.difference cur dest ^.. traverse <&> Deleting
    , Map.intersectionWith modify dest cur ^.. traverse
    ] & State
    where
        cur = currentFrame state ^. frameImagesMap <&> head
        dest = destFrame ^. frameImagesMap <&> markDuplicates
        add (key, destImg) =
            Modifying (destImg & iRect .~ curRect) (destImg ^. iRect)
            where
                destRect = destImg ^. iRect
                curRect =
                    findPrefix key curPrefixMap
                    & maybe (Rect (destRect ^. Rect.center) 0) genRect
                genRect prefix = relocateSubRect destRect (destPrefixMap ! prefix) (curPrefixMap ! prefix)
        modify destImg curImg =
            Modifying (destImg & iRect .~ curImg ^. iRect) (destImg ^. iRect)
        curPrefixMap = prefixRects cur
        destPrefixMap = prefixRects dest

stateMapIdentities :: (AnimId -> AnimId) -> State -> State
stateMapIdentities mapping =
    stateInterpolations . traverse . interpolationImage . iAnimId %~ mapping

-- When images are based on stale data (unloaded Font) we must clear them.
stateClearImages :: State -> State
stateClearImages =
    stateInterpolations . traverse . interpolationImage . iUnitImage .~ mempty

nextState :: R -> Maybe Frame -> State -> Maybe State
nextState movement Nothing state
    | all (Lens.has _Final) (state ^. stateInterpolations) = Nothing
    | otherwise = advanceState movement state & Just
nextState movement (Just dest) state =
    setNewDest dest state & advanceState movement & Just

{-# INLINE images #-}
images :: Lens.Traversal' Frame Image
images = frameImagesMap . Lens.traversed . Lens.traversed

{-# INLINE unitImages #-}
unitImages :: Lens.Traversal' Frame (Draw.Image ())
unitImages = images . iUnitImage

simpleFrame :: AnimId -> Draw.Image () -> Frame
simpleFrame animId image =
    Frame $ Map.singleton animId [Image animId image (Rect 0 1)]

sizedFrame :: AnimId -> Size -> Draw.Image () -> Frame
sizedFrame animId size =
    scale size .
    simpleFrame animId .
    (DrawUtils.scale (1 / size) %%)

instance Monoid Frame where
    mempty = Frame mempty
    mappend (Frame m0) (Frame m1) = Frame $ Map.unionWith (++) m0 m1

unitX :: Draw.Image ()
unitX = void $ mconcat
    [ Draw.line (0, 0) (1, 1)
    , Draw.line (1, 0) (0, 1)
    ]

red :: Draw.Color
red = Draw.Color 1 0 0 1

draw :: Frame -> Draw.Image ()
draw frame =
    frame
    ^. frameImagesMap
    & Map.elems
    <&> markConflicts
    & concat
    <&> posImage
    & mconcat
    where
        redX = Draw.tint red unitX
        markConflicts imgs@(_:_:_) =
            imgs <&> iUnitImage %~ mappend redX
        markConflicts imgs = imgs
        posImage (Image _ img rect) =
            DrawUtils.translate (rect ^. Rect.topLeft) %%
            DrawUtils.scale (rect ^. Rect.size) %%
            img

prefixRects :: Map AnimId Image -> Map AnimId Rect
prefixRects src =
    Map.fromList . filter (not . null . fst) . map perGroup $ groupOn fst $
    List.sortOn fst prefixItems
    where
        perGroup xs =
            (fst (head xs), List.foldl1' joinRects (map snd xs))
        prefixItems = do
            (key, img) <- Map.toList src
            prefix <- List.inits key
            return (prefix, img ^. iRect)
        joinRects a b =
            Rect {
                Rect._topLeft = tl,
                Rect._size = br - tl
            }
            where
                tl =
                    liftA2 min (a ^. Rect.topLeft) (b ^. Rect.topLeft)
                br =
                    liftA2 max (a ^. Rect.bottomRight) (b ^. Rect.bottomRight)

findPrefix :: Ord a => [a] -> Map [a] b -> Maybe [a]
findPrefix key dict =
    List.find (`Map.member` dict) . reverse $ List.inits key

relocateSubRect :: Rect -> Rect -> Rect -> Rect
relocateSubRect srcSubRect srcSuperRect dstSuperRect =
    Rect
    { Rect._topLeft =
              dstSuperRect ^. Rect.topLeft +
              sizeRatio *
              (srcSubRect ^. Rect.topLeft -
                srcSuperRect ^. Rect.topLeft)
    , Rect._size = sizeRatio * srcSubRect ^. Rect.size
    }
    where
        sizeRatio =
            dstSuperRect ^. Rect.size /
            fmap (max 1) (srcSuperRect ^. Rect.size)

mapIdentities :: (AnimId -> AnimId) -> Frame -> Frame
mapIdentities f =
    frameImagesMap %~ Map.fromList . map g . Map.toList
    where
        g (animId, imgs) = (f animId, imgs <&> iAnimId %~ f)

unitSquare :: AnimId -> Frame
unitSquare animId = simpleFrame animId DrawUtils.square

emptyRectangle :: Vector2 R -> Vector2 R -> AnimId -> Frame
emptyRectangle (Vector2 fX fY) totalSize@(Vector2 sX sY) animId =
    mconcat
    [ rect 0                      (Vector2 sX fY)
    , rect (Vector2 0 (sY - fY))  (Vector2 sX fY)
    , rect (Vector2 0 fY)         (Vector2 fX (sY - fY*2))
    , rect (Vector2 (sX - fX) fY) (Vector2 fX (sY - fY*2))
    ]
    & sizedFrame animId totalSize
    where
        rect origin size =
            DrawUtils.square
            & (DrawUtils.scale size %%)
            & (DrawUtils.translate origin %%)

backgroundColor :: AnimId -> Draw.Color -> Vector2 R -> Frame
backgroundColor animId color size =
    unitSquare animId
    & images . iUnitImage %~ Draw.tint color
    & scale size

translate :: Vector2 R -> Frame -> Frame
translate pos = images . iRect . Rect.topLeft +~ pos

scale :: Vector2 R -> Frame -> Frame
scale factor = images . iRect . Rect.topLeftAndSize *~ factor

-- Scale/translate a Unit-sized frame into a given rect
unitIntoRect :: Rect -> Frame -> Frame
unitIntoRect r =
    translate (r ^. Rect.topLeft) .
    scale (r ^. Rect.size)
