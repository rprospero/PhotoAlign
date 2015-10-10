{-# LANGUAGE OverloadedStrings #-}

-- | A program for aligning mounted samples and generating scripts for
-- an x-ray instrument

module Main (main) where

import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Haste.JSON
import Control.Error.Safe (rightMay)
import Control.Monad (liftM,(>=>))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT,runMaybeT))
import Data.IORef
import Data.Monoid

import Calibrate
import Scans
import JSON

data StateDump = StateDump {calib ::CalibState,
                            scandata ::ScanState}
instance JSONable StateDump where
    toJSON s = Dict . zip ["calib","scans"] $ [toJSON $ calib s, toJSON $ scandata s]
    fromJSON d = StateDump <$> (d ~~> "calib") <*> (d ~~> "scans")

-- | Default image file
image :: URL
image = "IndianRoller2.jpg"

-- | Given a file selection element, returns a URL to the selected file
getFilePath :: ElemID -> IO URL
getFilePath = ffi "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

-- | Given a file selection element, get the name of the returned file
getFileName :: ElemID -> IO String
getFileName = ffi "(function(x){return document.getElementById(x).value;})"

-- | Given a file element, reads the file into a text string.  Because
-- of the Javascript callback system, this string must then be passed
-- to an function exported by Haste under the name given in the
-- JSString.
readAsText :: JSString -> ElemID -> IO ()
readAsText = ffi "function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);}"

-- | The actual Photoalign program
main :: IO ()
main = do
  calibState <- initCalibState
  scanState <- initScanState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground
  imageName <- newIORef "IndianRoller2.jpg"
  mounts <- elemsByQS document "input[name='mount']"

  let action = updatePage scanState calibState background
      contrl = controller action scanState
      triggerController evt x = onEvent x evt $ const contrl

  export "processDump" (processDump calibState scanState)

  ignoreMaybeT $ do
         filePath <- MaybeT $ elemById "filePath"
         loadPath <- MaybeT $ elemById "loadPath"
         _ <- lift $ onEvent filePath Change $ updateBitmap action background imageName
         _ <- lift $ onEvent loadPath Change $ const $ readAsText "processDump" "loadPath"
         rots <- MaybeT $ elemById "rotations"
         stepSize <- MaybeT $ elemById "stepSize"


         can <- MaybeT $ getCanvasById "original"
         acan <- MaybeT $ getCanvasById "aligned"
         lift $ attachEvents calibState can action
         lift $ attachScanEvents scanState acan action
         upper <- MaybeT $ elemById "top"
         lower <- MaybeT $ elemById "bottom"
         offs <- MaybeT $ elemById "offset"

         lift $ mapM_ (triggerController Change) $ mounts ++ [stepSize,rots, upper, lower, offs]
         lift $ mapM_ (triggerController KeyDown) [stepSize, rots, upper, lower, offs]
  action

-- | Get the value from an element
valueById :: ElemID -> MaybeT IO String
valueById = MaybeT  . elemById >=> flip getProp "value"

setAttrById :: ElemID -> PropID -> String -> MaybeT IO ()
setAttrById e p v =  do
  el <- MaybeT $  elemById e
  setAttr el p v

-- | Read text inpure and update the global variables
controller :: IO () -> IORef ScanState -> IO ()
controller action s = do
  runMaybeT $ do
    r <- valueById "rotations"
    lift $ modifyIORef' s (\x -> x{rotations=map ((*(pi/180)) . read) . words$r})

  runMaybeT $ do
    size <- valueById "stepSize"
    lift $ modifyIORef' s (\x -> x{step=read size})

  runMaybeT $ do
    upper <- valueById "top"
    lower <- valueById "bottom"
    offs <- valueById "offset"
    [mount] <- elemsByQS document "input[name='mount']:checked"
    c <- getProp mount "value"

    lift $ modifyIORef' s (\x -> x{top=read upper,bottom=read lower,offset=read offs,choice=read c})

  action

-- | Loads a new image file
updateBitmap :: IO ()  -- ^ The generic page update to perform once the
             -> IORef Bitmap  -- ^ The IORef which stores the image
                             -- function has finished.
             -> IORef String  -- ^ The IORef which stores the name of the file
             -> ()
             -> IO ()
updateBitmap action background nameRef () = do
    getFilePath "filePath" >>= loadBitmap >>= writeIORef background

    imageName <- Main.getFileName "filePath"
    writeIORef nameRef imageName

    runMaybeT $ do
      setAttrById "saveLink" "download" $ imageName <> ".json"
      setAttrById "exportLink" "download" $ imageName <> ".txt"

    action

-- | Updates the global state to the values from the JSON file
processDump :: IORef CalibState -- ^ The global state of the calibration
              -> IORef ScanState -- ^ The global state of the scans
              -> JSString -- ^ The text of the JSON file
              -> IO ()
processDump c s result = ignoreMaybeT $ do
  d <- MaybeT . return $ (rightMay . decodeJSON) result >>= fromJSON
  lift $ writeIORef c $ calib d
  lift $ writeIORef s $ scandata d

  -- case decodeJSON result of
  --   Left _ -> return ()
  --   Right json -> case fromJSON json of
  --                  Just d -> do
  --                          writeIORef c $ calib d
  --                          writeIORef s $ scandata d
  --                  Nothing -> return ()

updatePage :: IORef ScanState -> IORef CalibState -> IORef Bitmap -> IO ()
updatePage scanState calibState background = do
  c <- readIORef calibState
  s <- readIORef scanState

  Just can1 <- getCanvasById "original"
  Just can2 <- getCanvasById "aligned"
  Just tbl <- elemById "scans"

  toggleExport s

  let action = updatePage scanState calibState background

  populateTable (updateTitle action scanState) (dropScan action scanState) s tbl

  drawAligned s c background can2
  drawCalibration c background can1

  fileSave "exportLink" $ toFile s
  fileSave "saveLink" . fromJSStr .  encodeJSON . toJSON $ StateDump c s

toggleExport :: ScanState -> IO ()
toggleExport s = let
    c = if scansReady s
        then ""
        else " disabled"
  in
    ignoreMaybeT $ setAttrById "exportLink" "class" $ "btn btn-primary" ++ c

drawCalibration :: CalibState -> IORef Bitmap -> Canvas -> IO ()
drawCalibration c background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.2,0.2) $ draw rawBackground (0,0)
    lineWidth 1 . color (RGB 255 0 255) . stroke $ boxShape c

drawAligned :: ScanState -> CalibState -> IORef Bitmap -> Canvas -> IO ()
drawAligned s c background can = do
  rawBackground <- readIORef background
  render can $ do
    alignImage (900,900) c $ scale (0.2,0.2) $ draw rawBackground (0,0)
    scanShape s
  return ()

fileSave :: ElemID -> String -> IO()
fileSave e contents = do
  encoded <- encodeURIComponent contents
  let uri = "data:text/plain;charset=utf-8," <> encoded
  ignoreMaybeT $ setAttrById e "href" uri

ignoreMaybeT :: (Monad m) => MaybeT m () -> m ()
ignoreMaybeT x = runMaybeT x >> return ()

encodeURIComponent :: String -> IO String
encodeURIComponent = ffi "encodeURIComponent"
