import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Data.IORef
import Data.String

import Calibrate
import Scans

image :: URL
image = "file:///home/adam/Science/sax-data/FeatherPhotos/IndianRoller2.jpg"

getFilePath :: ElemID -> IO URL
getFilePath = ffi $ Data.String.fromString "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

imageSize :: Point
imageSize = (3968,2232)

f >< (a,b) = (f a, f b)

-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  Just filePath <- elemById "filePath"
  Just tbl <- elemById "scans"
  calibState <- initCalibState
  scanState <- initScanState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground

  let action = updatePage scanState calibState background can acan tbl

  attachEvents calibState can action
  attachScanEvents scanState acan action

  onEvent filePath Change $ updateBitmap background
  return ()

updateBitmap :: IORef Bitmap -> () -> IO ()
updateBitmap background () = do
    image <- getFilePath "filePath"
    rawBackground <- loadBitmap image
    writeIORef background rawBackground

updatePage :: IORef ScanState -> IORef CalibState -> IORef Bitmap -> Canvas -> Canvas -> Elem -> IO ()
updatePage scanState state background can1 can2 tbl = do
  calib <- readIORef state
  scan <- readIORef scanState

  let action = updatePage scanState state background can1 can2 tbl

  populateTable (dropScan action scanState) scan tbl

  drawAligned scan calib background can2
  drawCalibration calib background can1

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
