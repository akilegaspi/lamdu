module Lamdu.Editor.Settings
    ( initial, newProp
    ) where

import           GUI.Momentu.Widgets.EventMapHelp (IsHelpShown(..))
import           Lamdu.Settings (Settings(..))
import qualified Lamdu.Themes as Themes
import qualified Control.Lens.Extended as Lens
import           Data.IORef
import           Data.Property (MkProperty')
import qualified Data.Property as Property
import           Lamdu.Config.Sampler (Sampler)
import qualified Lamdu.Config.Sampler as ConfigSampler
import qualified Lamdu.Eval.Manager as EvalManager
import qualified Lamdu.Settings as Settings
import           Lamdu.Sugar.Convert.Input (AnnotationMode(..))

import           Lamdu.Prelude

initial :: Themes.Selection -> AnnotationMode -> Settings
initial theme annotationMode =
    Settings
    { _sAnnotationMode = annotationMode
    , _sSelectedTheme = theme
    , _sHelpShown = HelpNotShown
    }

settingsChangeHandler :: Sampler -> EvalManager.Evaluator -> Maybe Settings -> Settings -> IO ()
settingsChangeHandler configSampler evaluator mOld new =
    do
        whenChanged Settings.sAnnotationMode $ \case
            Evaluation -> EvalManager.start evaluator
            _ -> EvalManager.stop evaluator
        whenChanged Settings.sSelectedTheme $ ConfigSampler.setTheme configSampler
    where
        whenChanged lens f =
            case mOld of
            Nothing -> f (new ^. lens)
            Just old -> when (old ^. lens /= new ^. lens) $ f (new ^. lens)

newProp :: Themes.Selection -> AnnotationMode -> Sampler -> EvalManager.Evaluator -> IO (MkProperty' IO Settings)
newProp theme annMode configSampler evaluator =
    do
        settingsChangeHandler configSampler evaluator Nothing initialSettings
        newIORef initialSettings <&> Property.fromIORef
            <&> Property.mkProperty . Lens.mapped .
                Lens.filteredBy Property.pVal <.> Property.pSet . Lens.imapped %@~
                \(oldVal, newVal) ->
                    -- Callback to notify update  AFTER we set the property:
                    (*> settingsChangeHandler configSampler evaluator (Just oldVal) newVal)
    where
        initialSettings = initial theme annMode
