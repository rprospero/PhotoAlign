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
import Data.IORef
import Data.Monoid
import Data.Maybe (fromJust)

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
  Just filePath <- elemById "filePath"
  Just loadPath <- elemById "loadPath"
  Just runfile <- elemById "runfile"
  Just rots <- elemById "rotations"
  calibState <- initCalibState
  scanState <- initScanState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground
  imageName <- newIORef "IndianRoller2.jpg"

  let action = updatePage scanState calibState background

  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  attachEvents calibState can action
  attachScanEvents scanState acan action

  export "processDump" (processDump calibState scanState)

  let contrl = controller action scanState


  Just upper <- elemById "top"
  Just lower <- elemById "bottom"
  Just offs <- elemById "offset"
  mounts <- elemsByQS document "input[name='mount']"
  -- Just choice <- elemById "mount"

  let triggerController evt x = onEvent x evt $ const $ contrl

  _ <- onEvent filePath Change $ updateBitmap action background imageName
  _ <- onEvent loadPath Change $ const $ readAsText "processDump" "loadPath"
  mapM_ (triggerController Change) $ concat [mounts, [runfile, rots, upper, lower, offs]]
  mapM_ (triggerController KeyDown) [runfile, rots, upper, lower, offs]
  action

-- | Read text inpure and update the global variables
controller :: IO () -> IORef ScanState -> IO ()
controller action s = do
  Just runfile <- elemById "runfile"
  Just rots <- elemById "rotations"

  f <- getProp runfile "value"
  modifyIORef' s (\x -> x{fileName=f})

  r <- getProp rots "value"
  modifyIORef' s (\x -> x{rotations=map ((*(pi/180)) . read) . words$r})

  upper <- (fromJust <$> elemById "top") >>= flip getProp "value"
  lower <- (fromJust <$> elemById "bottom") >>= flip getProp "value"
  offs <- (fromJust <$> elemById "offset") >>= flip getProp "value"

  modifyIORef' s (\x -> x{top=read upper,bottom=read lower,offset=read offs})

  action

-- | Loads a new image file
updateBitmap :: IO ()  -- ^ The generic page update to perform once the
             -> IORef Bitmap  -- ^ The IORef which stores the image
                             -- function has finished.
             -> IORef String  -- ^ The IORef which stores the name of the file
             -> ()
             -> IO ()
updateBitmap action background nameRef () = do
    imagePath <- getFilePath "filePath"
    rawBackground <- loadBitmap imagePath
    writeIORef background rawBackground
    imageName <- Main.getFileName "filePath"
    writeIORef nameRef imageName
    Just saveLink <- elemById "saveLink"
    setAttr saveLink "download" $ imageName <> ".json"

    Just exportLink <- elemById "exportLink"
    setAttr exportLink "download" $ imageName <> ".txt"
    action

-- | Updates the global state to the values from the JSON file
processDump :: IORef CalibState -- ^ The global state of the calibration
              -> IORef ScanState -- ^ The global state of the scans
              -> JSString -- ^ The text of the JSON file
              -> IO ()
processDump c s result =
  case decodeJSON result of
    Left _ -> return ()
    Right json -> case fromJSON json of
                   Just d -> do
                           writeIORef c $ calib d
                           writeIORef s $ scandata d
                   Nothing -> return ()

updatePage :: IORef ScanState -> IORef CalibState -> IORef Bitmap -> IO ()
updatePage scanState calibState background = do
  c <- readIORef calibState
  s <- readIORef scanState

  Just can1 <- getCanvasById "original"
  Just can2 <- getCanvasById "aligned"
  Just tbl <- elemById "scans"
  Just runFile <- elemById "runfile"

  setProp runFile "value" $ fileName s

  toggleExport s

  let action = updatePage scanState calibState background

  populateTable (updateTitle action scanState) (dropScan action scanState) s tbl

  drawAligned s c background can2
  drawCalibration c background can1

  fileSave "exportLink" $ toFile s
  fileSave "saveLink" . fromJSStr .  encodeJSON . toJSON $ StateDump c s

toggleExport :: ScanState -> IO ()
toggleExport s = do
  Just b <- elemById "exportLink"
  case scansReady s of
    True -> setAttr b "class" "btn btn-primary"
    False -> setAttr b "class" "btn btn-primary disabled"

drawCalibration :: CalibState -> IORef Bitmap -> Canvas -> IO ()
drawCalibration c background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.3,0.3) $ draw rawBackground (0,0)
    lineWidth 1 . color (RGB 255 0 255) . stroke $ boxShape c

drawAligned :: ScanState -> CalibState -> IORef Bitmap -> Canvas -> IO ()
drawAligned s c background can = do
  rawBackground <- readIORef background
  render can $ do
    alignImage (900,900) c $ scale (0.3,0.3) $ draw rawBackground (0,0)
    scanShape s
  return ()

fileSave :: ElemID -> String -> IO()
fileSave e contents = do
  Just el <- elemById e
  encoded <- encodeURIComponent contents
  let uri = "data:text/plain;charset=utf-8," <> encoded
  setAttr el "href" uri

encodeURIComponent :: String -> IO String
encodeURIComponent = ffi "encodeURIComponent"
