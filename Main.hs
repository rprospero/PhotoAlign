import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Data.List (elemIndex,minimum)
import Data.IORef
import Data.String

image :: URL
image = "file:///home/adam/Science/sax-data/FeatherPhotos/IndianRoller2.jpg"

getFilePath :: ElemID -> IO URL
getFilePath = ffi $ Data.String.fromString "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

imageSize :: Point
imageSize = (3968,2232)

f >< (a,b) = (f a, f b)

data Corner = NW | NE | SW | SE
data MouseState = Free | Dragging Corner
data BoxMap = BoxMap Point Point Point Point

data CalibState = CalibState {mouse ::MouseState,
                              box :: BoxMap}
defaultCalibState = CalibState Free $ BoxMap (0,0) (0,50) (50,50) (50,0)

makeFree :: CalibState -> CalibState
makeFree (CalibState _ b) = CalibState Free b

dist :: Point -> Point -> Double
dist (x1,y1) (x2,y2) = (x1-x2)^2+(y1-y2)^2

startDrag :: Point -> CalibState -> CalibState
startDrag p (CalibState _ box@(BoxMap a b c d)) = CalibState (Dragging corner) box
    where
      dists = map (dist p) [a,b,c,d]
      corner = case elemIndex (minimum dists) dists of
                     Just 0 -> NW
                     Just 1 -> SW
                     Just 2 -> SE
                     Just 3 -> NE
                     Nothing -> SE -- Shouldn't happen




mNull :: Monad m => a -> m (a,())
mNull x = return (x, ())

-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  Just filePath <- elemById "filePath"
  calibState <- newIORef defaultCalibState
  rawBackground <- loadBitmap image
  background <- newIORef rawBackground

  let action = updatePage calibState background can acan

  onEvent can MouseDown $ mouseDown action calibState
  onEvent can MouseUp $ mouseUp action calibState
  onEvent can MouseMove $ mouseMove action calibState

  onEvent filePath Change $ updateBitmap background
  return ()
  -- onEvent can MouseMove mouseMove
  -- drawCanvas background
  -- animate background acan 2

updateBitmap :: IORef Bitmap -> () -> IO ()
updateBitmap background () = do
    image <- getFilePath "filePath"
    rawBackground <- loadBitmap image
    writeIORef background rawBackground

mouseUp :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseUp action state mouse = do
  modifyIORef' state makeFree
  action

mouseDown :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseDown action state mouse = do
  modifyIORef' state $ \x -> let p = floatPair (mouseCoords mouse)
                            in startDrag p x
  action

mouseMove :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseMove action state mouse = do
  modifyIORef' state $ mouseMove' (floatPair $ mouseCoords mouse)
  action

mouseMove' :: Point -> CalibState -> CalibState
mouseMove' _ st@(CalibState Free _) = st
mouseMove' stop (CalibState ms@(Dragging NE) (BoxMap a b c _)) =
    CalibState ms (BoxMap a b c stop)
mouseMove' stop (CalibState ms@(Dragging SE) (BoxMap a b _ d)) =
    CalibState ms (BoxMap a b stop d)
mouseMove' stop (CalibState ms@(Dragging SW) (BoxMap a _ c d)) =
    CalibState ms (BoxMap a stop c d)
mouseMove' stop (CalibState ms@(Dragging NW) (BoxMap _ b c d)) =
    CalibState ms (BoxMap stop b c d)

boxMove' :: Point -> BoxMap -> IO (BoxMap, ())
boxMove' p (BoxMap a b _ d) = return (BoxMap a b p d,())

updatePage :: IORef CalibState -> IORef Bitmap -> Canvas -> Canvas -> IO ()
updatePage state background can1 can2 = do
  calib <- readIORef state

  drawCanvas (box calib) background can2
  drawLines (box calib) background can1

drawLines :: BoxMap -> IORef Bitmap -> Canvas -> IO ()
drawLines (BoxMap a b c d) background can = do
  rawBackground <- readIORef background
  render can $ do
    scale (0.1,0.1) $ draw rawBackground (0,0)
    lineWidth 1 . stroke $ do
                 line a b
                 line b c
                 line c d
                 line d a

rotateAboutCenter :: Point -> Double -> Picture () -> Picture ()
rotateAboutCenter center angle = translate ((/2) >< center) . rotate (-angle) . translate ((/(-2)) >< center)

drawCanvas :: BoxMap -> IORef Bitmap -> Canvas -> IO ()
drawCanvas box background can = do
  let angle = getAngle box
  rawBackground <- readIORef background
  render can $ do
    rotateAboutCenter ((/ 20) >< imageSize) angle $ scale (0.1,0.1) $ draw rawBackground (0,0)
    color (RGBA 0 0 255 0.5) . font "20px Bitstream Vera" $ text (10, 160) $ show (180/pi*angle)
  return ()

getAngle :: BoxMap -> Double
getAngle (BoxMap a b c d) = atan $ (s1+s2+s3+s4)/4
    where
      s1 = tan $ slope a b-pi/2
      s2 = tan $ slope b c
      s3 = tan $ slope c d+pi/2
      s4 = tan $ slope d a-pi

slope :: Point -> Point -> Double
slope (x1,y1) (x2,y2) = atan2 (y2-y1) (x2-x1)

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)
