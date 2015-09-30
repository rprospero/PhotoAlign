{-# LANGUAGE OverloadedStrings #-}

import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Haste.JSON
import Data.IORef
import Data.String
import Data.Monoid

import Calibrate
import Scans
import JSON

data StateDump = StateDump {calib ::CalibState,
                            scandata ::ScanState}
instance JSONable StateDump where
    toJSON s = Dict . zip ["calib","scans"] $ [toJSON $ calib s, toJSON $ scandata s]
    fromJSON d = StateDump <$> (d ~~> "calib") <*> (d ~~> "scans")

image :: URL
image = "file:///home/adam/Science/sax-data/FeatherPhotos/IndianRoller2.jpg"

getFilePath :: ElemID -> IO URL
getFilePath = ffi $ Data.String.fromString "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

readAsText :: JSString -> ElemID -> IO ()
readAsText = ffi $ "function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);}"

-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  Just filePath <- elemById "filePath"
  Just loadPath <- elemById "loadPath"
  Just tbl <- elemById "scans"
  calibState <- initCalibState
  scanState <- initScanState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground

  let action = updatePage scanState calibState background can acan tbl

  attachEvents calibState can action
  attachScanEvents scanState acan action

  export "processDump" (processDump calibState scanState)

  _ <- onEvent filePath Change $ updateBitmap background
  _ <- onEvent loadPath Change $ const $ readAsText "processDump" "loadPath"
  return ()

updateBitmap :: IORef Bitmap -> () -> IO ()
updateBitmap background () = do
    imagePath <- getFilePath "filePath"
    rawBackground <- loadBitmap imagePath
    writeIORef background rawBackground

processDump :: IORef CalibState -> IORef ScanState -> JSString -> IO ()
processDump c s result = do
  case decodeJSON result of
    Left _ -> print "Undecoded" >> print result
    Right json -> case fromJSON json of
                   Just d -> do
                           writeIORef c $ calib d
                           writeIORef s $ scandata d
                   Nothing -> print "Unparsed" >> print result

updatePage :: IORef ScanState -> IORef CalibState -> IORef Bitmap -> Canvas -> Canvas -> Elem -> IO ()
updatePage scanState state background can1 can2 tbl = do
  calib <- readIORef state
  scan <- readIORef scanState

  let action = updatePage scanState state background can1 can2 tbl

  populateTable (dropScan action scanState) scan tbl

  drawAligned scan calib background can2
  drawCalibration calib background can1

  fileSave "exportLink" $ toFile scan
  fileSave "saveLink" . fromJSStr .  encodeJSON . toJSON $ StateDump calib scan

drawCalibration :: CalibState -> IORef Bitmap -> Canvas -> IO ()
drawCalibration calib background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.1,0.1) $ draw rawBackground (0,0)
    lineWidth 1 . stroke $ boxShape calib

drawAligned :: ScanState -> CalibState -> IORef Bitmap -> Canvas -> IO ()
drawAligned scan calib background can = do
  rawBackground <- readIORef background
  render can $ do
    alignImage (400,400) calib $ scale (0.1,0.1) $ draw rawBackground (0,0)
    scanShape scan
  return ()

fileSave :: ElemID -> String -> IO()
fileSave e contents = do
  Just elem <- elemById e
  encoded <- encodeURIComponent contents
  let uri = "data:text/plain;charset=utf-8," <> encoded
  setAttr elem "href" uri

encodeURIComponent :: String -> IO String
encodeURIComponent = ffi (Data.String.fromString "encodeURIComponent")
