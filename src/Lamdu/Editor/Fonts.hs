module Lamdu.Editor.Fonts
    ( makeGetFonts
    ) where

import qualified Control.Lens.Extended as Lens
import           Data.MRUMemo (memoIO)
import qualified GUI.Momentu as M
import           Lamdu.Config.Sampler (sTheme)
import qualified Lamdu.Config.Sampler as ConfigSampler
import           Lamdu.Config.Theme (Theme(..))
import qualified Lamdu.Config.Theme as Theme
import           Lamdu.Config.Theme.Fonts (FontSize, Fonts(..))
import qualified Lamdu.Config.Theme.Fonts as Fonts
import qualified Lamdu.Font as Font
import           System.FilePath ((</>))
import qualified System.FilePath as FilePath

import           Lamdu.Prelude

prependConfigPath :: ConfigSampler.Sample -> Fonts FilePath -> Fonts FilePath
prependConfigPath sample =
    Lens.mapped %~ f
    where
        dir = FilePath.takeDirectory (sample ^. ConfigSampler.sConfigPath)
        f "" = "" -- Debug font!
        f x = dir </> x

assignFontSizes :: Theme -> Fonts FilePath -> Fonts (FontSize, FilePath)
assignFontSizes theme fonts =
    fonts
    <&> (,) baseTextSize
    & Fonts.help . _1 .~ helpTextSize
    where
        baseTextSize = theme ^. Theme.baseTextSize
        helpTextSize = theme ^. Theme.help . Theme.helpTextSize

curSampleFonts :: ConfigSampler.Sample -> Fonts (FontSize, FilePath)
curSampleFonts sample =
    sample ^. sTheme . Theme.fonts
    & prependConfigPath sample
    & assignFontSizes (sample ^. sTheme)

defaultFontPath :: FilePath -> FilePath
defaultFontPath configPath =
    configDir </> "fonts/Purisa.ttf"
    where
        configDir = FilePath.takeDirectory configPath

makeGetFonts ::
    Font.LCDSubPixelEnabled ->
    IO (M.Zoom -> ConfigSampler.Sample -> IO (Fonts M.Font))
makeGetFonts subpixel =
    Font.new subpixel & uncurry & memoIO
    <&> f
    where
        f cachedLoadFonts zoom sample =
            do
                sizeFactor <- M.getZoomFactor zoom
                cachedLoadFonts
                    ( defaultFontPath (sample ^. ConfigSampler.sConfigPath)
                    , curSampleFonts sample <&> _1 *~ sizeFactor
                    )
