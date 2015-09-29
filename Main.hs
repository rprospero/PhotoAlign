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
  calibState <- initCalibState
  scanState <- initScanState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground

  let action = updatePage scanState calibState background can acan

  attachEvents calibState can action
  attachScanEvents scanState acan action

  onEvent filePath Change $ updateBitmap background
  return ()

updateBitmap :: IORef Bitmap -> () -> IO ()
updateBitmap background () = do
    image <- getFilePath "filePath"
    rawBackground <- loadBitmap image
    writeIORef background rawBackground

updatePage :: IORef ScanState -> IORef CalibState -> IORef Bitmap -> Canvas -> Canvas -> IO ()
updatePage scan state background can1 can2 = do
  calib <- readIORef state
  scan <- readIORef scan

  drawAligned scan calib background can2
  drawCalibration calib background can1

drawCalibration :: CalibState -> IORef Bitmap -> Canvas -> IO ()
drawCalibration calib background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.1,0.1) $ draw rawBackground (0,0)
    lineWidth 1 . stroke $ boxShape calib

rotateAboutCenter :: Point -> Double -> Picture () -> Picture ()
rotateAboutCenter center angle = translate ((/2) >< center) . rotate (-angle) . translate ((/(-2)) >< center)

drawAligned :: ScanState -> CalibState -> IORef Bitmap -> Canvas -> IO ()
drawAligned scan calib background can = do
  let angle = getAngle calib
  rawBackground <- readIORef background
  render can $ do
    rotateAboutCenter ((/ 20) >< imageSize) angle $ scale (0.1,0.1) $ draw rawBackground (0,0)
    lineWidth 1 . stroke $ scanShape scan
  return ()
