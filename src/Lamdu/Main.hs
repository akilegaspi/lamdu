{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, Rank2Types, DisambiguateRecordFields, NamedFieldPuns #-}
module Main
    ( main
    ) where

import           Control.Concurrent.MVar
import qualified Control.Exception as E
import qualified Control.Lens as Lens
import           Control.Monad (join, replicateM_)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.CurAndPrev (current)
import           Data.IORef
import           Data.MRUMemo (memoIO)
import qualified Data.Monoid as Monoid
import           Data.Store.Db (Db)
import           Data.Store.Transaction (Transaction)
import qualified Data.Store.Transaction as Transaction
import           GHC.Conc (setNumCapabilities, getNumProcessors)
import           GHC.Stack (whoCreated)
import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.Rendering.OpenGL.GL as GL
import           Graphics.UI.Bottle.Main (mainLoopWidget)
import qualified Graphics.UI.Bottle.Main as MainLoop
import           Graphics.UI.Bottle.Widget (Widget)
import qualified Graphics.UI.Bottle.Widget as Widget
import           Graphics.UI.Bottle.Zoom (Zoom)
import qualified Graphics.UI.Bottle.Zoom as Zoom
import qualified Graphics.UI.GLFW as GLFW
import qualified Graphics.UI.GLFW.Utils as GLFWUtils
import           Lamdu.Config (Config)
import qualified Lamdu.Config as Config
import           Lamdu.Config.Sampler (Sampler, sConfig, sTheme)
import qualified Lamdu.Config.Sampler as ConfigSampler
import           Lamdu.Config.Theme (Theme(..))
import qualified Lamdu.Config.Theme as Theme
import qualified Lamdu.Data.DbInit as DbInit
import qualified Lamdu.Data.DbLayout as DbLayout
import           Lamdu.Data.Export.Codejam (exportFancy)
import qualified Lamdu.Data.Export.JSON as Export
import qualified Lamdu.Eval.Manager as EvalManager
import           Lamdu.Eval.Results (EvalResults)
import           Lamdu.Expr.IRef (ValI)
import           Lamdu.Font (FontSize, Fonts(..))
import qualified Lamdu.Font as Font
import           Lamdu.GUI.CodeEdit.Settings (Settings(..))
import qualified Lamdu.GUI.CodeEdit.Settings as Settings
import qualified Lamdu.GUI.Main as GUIMain
import qualified Lamdu.Opts as Opts
import qualified Lamdu.Style as Style
import           Lamdu.Themes (defaultTheme, themeEventMap)
import qualified Lamdu.VersionControl as VersionControl
import           Lamdu.VersionControl.Actions (mUndo)
import qualified System.Directory as Directory
import           System.FilePath ((</>))
import qualified System.FilePath as FilePath
import           System.IO (hPutStrLn, stderr)

import           Lamdu.Prelude

type T = Transaction

defaultFontPath :: ConfigSampler.Sample -> FilePath
defaultFontPath sample =
    configDir </> "fonts/Purisa.ttf"
    where
        configDir = FilePath.takeDirectory (sample ^. ConfigSampler.sConfigPath)

getLamduDir :: IO FilePath
getLamduDir = Directory.getHomeDirectory <&> (</> ".lamdu")

main :: IO ()
main =
    do
        setNumCapabilities =<< getNumProcessors
        Opts.Parsed{_pLamduDB,_pCommand} <- Opts.get
        lamduDir <- maybe getLamduDir return _pLamduDB
        let withDB = DbInit.withDB lamduDir
        case _pCommand of
            Opts.DeleteDb -> deleteDB lamduDir
            Opts.Undo n -> withDB (undoN n)
            Opts.Editor opts -> withDB $ runEditor opts
    `E.catch` \e@E.SomeException{} -> do
    hPutStrLn stderr $ "Main exiting due to exception: " ++ show e
    mapM_ (hPutStrLn stderr) =<< whoCreated e
    return ()

deleteDB :: FilePath -> IO ()
deleteDB lamduDir =
    do
        putStrLn "Deleting DB..."
        Directory.removeDirectoryRecursive lamduDir

undoN :: Int -> Db -> IO ()
undoN n db =
    do
        putStrLn $ "Undoing " ++ show n ++ " times"
        DbLayout.runDbTransaction db $ replicateM_ n undo
    where
        undo =
            do
                actions <- VersionControl.makeActions
                fromMaybe (fail "Cannot undo any further") $ mUndo actions

createWindow :: String -> Opts.WindowMode -> IO GLFW.Window
createWindow title mode =
    do
        monitor <-
            GLFW.getPrimaryMonitor
            >>= maybe (fail "GLFW: Can't get primary monitor") return
        videoModeSize <- GLFWUtils.getVideoModeSize monitor
        let createWin = GLFWUtils.createWindow title
        case mode of
            Opts.FullScreen         -> createWin (Just monitor) videoModeSize
            Opts.VideoModeSize      -> createWin Nothing videoModeSize

settingsChangeHandler :: EvalManager.Evaluator -> Settings -> IO ()
settingsChangeHandler evaluator settings =
    case settings ^. Settings.sInfoMode of
    Settings.Evaluation -> EvalManager.start evaluator
    _ -> EvalManager.stop evaluator

exportActions ::
    Config -> EvalResults (ValI DbLayout.ViewM) -> GUIMain.ExportActions DbLayout.ViewM
exportActions config evalResults =
    GUIMain.ExportActions
    { GUIMain.exportRepl = fileExport Export.fileExportRepl
    , GUIMain.exportAll = fileExport Export.fileExportAll
    , GUIMain.exportFancy = export (exportFancy evalResults)
    , GUIMain.exportDef = fileExport . Export.fileExportDef
    , GUIMain.importAll = importAll
    }
    where
        Config.Export{exportPath} = Config.export config
        export x = x <&> flip (,) () & return & GUIMain.M
        fileExport exporter = exporter exportPath & export
        importAll path = Export.fileImportAll path <&> fmap ((,) (pure ())) & GUIMain.M

makeRootWidget ::
    Fonts Draw.Font -> Db -> IORef Settings -> EvalManager.Evaluator ->
    Config -> Theme -> Widget.Size -> IO (Widget (MainLoop.M Widget.EventResult))
makeRootWidget fonts db settingsRef evaluator config theme size =
    do
        cursor <-
            DbLayout.cursor DbLayout.revisionProps
            & Transaction.getP
            & DbLayout.runDbTransaction db
        eventMap <- Settings.mkEventMap (settingsChangeHandler evaluator) config settingsRef
        evalResults <- EvalManager.getResults evaluator
        settings <- readIORef settingsRef
        let env = GUIMain.Env
                { _envEvalRes = evalResults
                , _envExportActions =
                    exportActions config (evalResults ^. current)
                , _envConfig = config
                , _envTheme = theme
                , _envSettings = settings
                , _envStyle = Style.style theme fonts
                , _envFullSize = size
                , _envCursor = cursor
                }
        let dbToIO action =
                case settings ^. Settings.sInfoMode of
                Settings.Evaluation ->
                    EvalManager.runTransactionAndMaybeRestartEvaluator evaluator action
                _ -> DbLayout.runDbTransaction db action
        mkWidgetWithFallback dbToIO env
            <&> Widget.weakerEvents (eventMap <&> liftIO)

withMVarProtection :: a -> (MVar (Maybe a) -> IO b) -> IO b
withMVarProtection val =
    E.bracket (newMVar (Just val)) (\mvar -> modifyMVar_ mvar (\_ -> return Nothing))

printGLVersion :: IO ()
printGLVersion =
    do
        ver <- GL.get GL.glVersion
        putStrLn $ "Using GL version: " ++ show ver

runEditor :: Opts.EditorOpts -> Db -> IO ()
runEditor opts db =
    do
        -- Load config as early as possible, before we open any windows/etc
        themeRef <- newIORef defaultTheme
        configSampler <- ConfigSampler.new defaultTheme

        GLFWUtils.withGLFW $ do
            win <-
                createWindow
                (opts ^. Opts.eoWindowTitle)
                (opts ^. Opts.eoWindowMode)
            printGLVersion
            refreshScheduler <- newRefreshScheduler
            withMVarProtection db $ \dbMVar ->
                do
                    evaluator <-
                        EvalManager.new EvalManager.NewParams
                        { EvalManager.resultsUpdated = scheduleRefresh refreshScheduler
                        , EvalManager.dbMVar = dbMVar
                        , EvalManager.copyJSOutputPath = opts ^. Opts.eoCopyJSOutputPath
                        }
                    let initialSettings = Settings Settings.defaultInfoMode
                    settingsRef <- newIORef initialSettings
                    settingsChangeHandler evaluator initialSettings
                    mainLoop subpixel win refreshScheduler configSampler $
                        \fonts config theme size ->
                        let themeEvents =
                                themeEventMap (Config.changeThemeKeys config) configSampler themeRef
                                <&> liftIO
                        in  makeRootWidget fonts db settingsRef evaluator
                            config theme size
                            <&> Widget.weakerEvents themeEvents
    where
        subpixel
            | opts ^. Opts.eoSubpixelEnabled = Font.LCDSubPixelEnabled
            | otherwise = Font.LCDSubPixelDisabled

newtype RefreshScheduler = RefreshScheduler (IORef Bool)
newRefreshScheduler :: IO RefreshScheduler
newRefreshScheduler = newIORef False <&> RefreshScheduler
isRefreshScheduled :: RefreshScheduler -> IO Bool
isRefreshScheduled (RefreshScheduler ref) = atomicModifyIORef ref $ \r -> (False, r)
scheduleRefresh :: RefreshScheduler -> IO ()
scheduleRefresh (RefreshScheduler ref) = writeIORef ref True

prependConfigPath :: ConfigSampler.Sample -> Fonts FilePath -> Fonts FilePath
prependConfigPath sample =
    Lens.mapped %~ (dir </>)
    where
        dir = FilePath.takeDirectory (sample ^. ConfigSampler.sConfigPath)

assignFontSizes :: Theme -> Fonts FilePath -> Fonts (FontSize, FilePath)
assignFontSizes theme fonts =
    fonts
    <&> (,) baseTextSize
    & Font.lfontHelp . _1 .~ helpTextSize
    where
        baseTextSize = Theme.baseTextSize theme
        helpTextSize = Theme.helpTextSize (Theme.help theme)

curSampleFonts :: ConfigSampler.Sample -> Fonts (FontSize, FilePath)
curSampleFonts sample =
    sample ^. sTheme
    & Theme.fonts
    & prependConfigPath sample
    & assignFontSizes (sample ^. sTheme)

makeGetFonts ::
    Font.LCDSubPixelEnabled ->
    IO (Zoom -> ConfigSampler.Sample -> IO (Fonts Draw.Font))
makeGetFonts subpixel =
    Font.new subpixel & uncurry & memoIO
    <&> f
    where
        f cachedLoadFonts zoom sample =
            do
                sizeFactor <- Zoom.getSizeFactor zoom
                cachedLoadFonts
                    ( defaultFontPath sample
                    , curSampleFonts sample <&> _1 *~ sizeFactor
                    )

mainLoop ::
    Font.LCDSubPixelEnabled ->
    GLFW.Window -> RefreshScheduler -> Sampler ->
    (Fonts Draw.Font -> Config -> Theme -> Widget.Size ->
    IO (Widget (MainLoop.M Widget.EventResult))) -> IO ()
mainLoop subpixel win refreshScheduler configSampler iteration =
    do
        getFonts <- makeGetFonts subpixel
        lastVersionNumRef <- newIORef []
        let makeWidget zoom size =
                do
                    sample <- ConfigSampler.getSample configSampler
                    fonts <- getFonts zoom sample
                    iteration fonts (sample ^. sConfig) (sample ^. sTheme) size
        mainLoopWidget win makeWidget MainLoop.Options
            { getConfig =
                do
                    sample <- ConfigSampler.getSample configSampler
                    Style.mainLoopConfig (sample ^. sConfig) (sample ^. sTheme)
                        & return
            , tickHandler =
                do
                    curVersionNum <-
                        ConfigSampler.getSample configSampler
                        <&> ConfigSampler.sVersion
                    configChanged <- atomicModifyIORef lastVersionNumRef $
                        \lastVersionNum ->
                        (curVersionNum, lastVersionNum /= curVersionNum)
                    if configChanged
                        then return True
                        else isRefreshScheduled refreshScheduler
            , getHelpStyle =
                \zoom ->
                do
                    sample <- ConfigSampler.getSample configSampler
                    fonts <- getFonts zoom sample
                    let helpConfig = sample ^. sConfig & Config.help
                    let helpTheme = sample ^. sTheme & Theme.help
                    Style.help (Font.fontHelp fonts) helpConfig helpTheme
                        & return
            }

mkWidgetWithFallback ::
    (forall a. T DbLayout.DbM a -> IO a) ->
    GUIMain.Env -> IO (Widget (MainLoop.M Widget.EventResult))
mkWidgetWithFallback dbToIO env =
    do
        (isValid, widget) <-
            dbToIO $
            do
                candidateWidget <- makeMainGui dbToIO env
                (isValid, widget) <-
                    if Widget.isFocused candidateWidget
                    then return (True, candidateWidget)
                    else do
                        finalWidget <-
                            env & GUIMain.envCursor .~ GUIMain.defaultCursor
                            & makeMainGui dbToIO
                        Transaction.setP (DbLayout.cursor DbLayout.revisionProps)
                            GUIMain.defaultCursor
                        return (False, finalWidget)
                unless (Widget.isFocused widget) $
                    fail "Root cursor did not match"
                return (isValid, widget)
        unless isValid $ putStrLn $ "Invalid cursor: " ++ show (env ^. GUIMain.envCursor)
        widget
            & Widget.backgroundColor ["background"] (bgColor isValid theme)
            & return
    where
        theme = env ^. GUIMain.envTheme
        bgColor False = Theme.invalidCursorBGColor
        bgColor True = Theme.backgroundColor

makeMainGui ::
    (forall a. T DbLayout.DbM a -> IO a) ->
    GUIMain.Env -> T DbLayout.DbM (Widget (MainLoop.M Widget.EventResult))
makeMainGui dbToIO env =
    GUIMain.make env
    <&> Widget.events %~ \act ->
    act ^. GUIMain.m
    & Lens.mapped %~ (>>= _2 attachCursor)
    <&> dbToIO
    & join
    <&> uncurry MainLoop.EventResult & MainLoop.M
    where
        attachCursor eventResult =
            eventResult ^. Widget.eCursor
            & Monoid.getLast
            & maybe (return ())
              (Transaction.setP (DbLayout.cursor DbLayout.revisionProps))
            & (eventResult <$)
