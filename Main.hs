{-# LANGUAGE OverloadedStrings #-}

import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Haste.JSON
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

image :: URL
image = "IndianRoller2.jpg"

getFilePath :: ElemID -> IO URL
getFilePath = ffi "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

getFileName :: ElemID -> IO String
getFileName = ffi "(function(x){return document.getElementById(x).value;})"

readAsText :: JSString -> ElemID -> IO ()
readAsText = ffi "function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);}"

-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just filePath <- elemById "filePath"
  Just loadPath <- elemById "loadPath"
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

  _ <- onEvent filePath Change $ updateBitmap action background imageName
  _ <- onEvent loadPath Change $ const $ readAsText "processDump" "loadPath"
  action

updateBitmap :: IO () -> IORef Bitmap -> IORef String -> () -> IO ()
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

processDump :: IORef CalibState -> IORef ScanState -> JSString -> IO ()
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

  let action = updatePage scanState calibState background

  populateTable (dropScan action scanState) s tbl

  drawAligned s c background can2
  drawCalibration c background can1

  fileSave "exportLink" $ toFile "title" s
  fileSave "saveLink" . fromJSStr .  encodeJSON . toJSON $ StateDump c s

drawCalibration :: CalibState -> IORef Bitmap -> Canvas -> IO ()
drawCalibration c background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.1,0.1) $ draw rawBackground (0,0)
    lineWidth 1 . stroke $ boxShape c

drawAligned :: ScanState -> CalibState -> IORef Bitmap -> Canvas -> IO ()
drawAligned s c background can = do
  rawBackground <- readIORef background
  render can $ do
    alignImage (400,400) c $ scale (0.1,0.1) $ draw rawBackground (0,0)
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
