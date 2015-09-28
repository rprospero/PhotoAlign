import Haste
import Haste.App (MonadIO)
import Haste.Concurrent
import Haste.Events
import Haste.Graphics.Canvas
import Data.Maybe (fromMaybe)
import Data.List (findIndex,minimum)

image :: URL
image = "http://imgs.xkcd.com/comics/nasa_press_conference.png"

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
      corner = case findIndex (== minimum dists) dists of
                     Just 0 -> NW
                     Just 1 -> SW
                     Just 2 -> SE
                     Just 3 -> NE
                     Nothing -> SE -- Shouldn't happen




mNull :: Monad m => a -> m (a,())
mNull x = return (x, ())

-- | Then you grab a canvas object...
main :: IO ()
main = concurrent $ do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  calibState <- newMVar defaultCalibState
  background <- loadBitmap image

  let action = updatePage calibState background can acan

  onEvent can MouseDown $ mouseDown action calibState
  onEvent can MouseUp $ mouseUp action calibState
  onEvent can MouseMove $ mouseMove action calibState
  return ()
  -- onEvent can MouseMove mouseMove
  -- drawCanvas background
  -- animate background acan 2

mouseUp :: CIO () -> MVar CalibState -> MouseData -> CIO ()
mouseUp action state mouse = do
  modifyMVarIO state $ mNull . makeFree
  action

mouseDown :: CIO () -> MVar CalibState -> MouseData -> CIO ()
mouseDown action state mouse = do
  modifyMVarIO state $ \x -> let p = floatPair (mouseCoords mouse)
                            in mNull (startDrag p x)
  action

mouseMove :: CIO () -> MVar CalibState -> MouseData -> CIO ()
mouseMove action state mouse = do
  modifyMVarIO state $ mouseMove' (floatPair $ mouseCoords mouse)
  action

mouseMove' :: Point -> CalibState -> IO (CalibState, ())
mouseMove' _ st@(CalibState Free _) = mNull st
mouseMove' stop (CalibState ms@(Dragging NE) (BoxMap a b c _)) =
    mNull (CalibState ms (BoxMap a b c stop))
mouseMove' stop (CalibState ms@(Dragging SE) (BoxMap a b _ d)) =
    mNull (CalibState ms (BoxMap a b stop d))
mouseMove' stop (CalibState ms@(Dragging SW) (BoxMap a _ c d)) =
    mNull (CalibState ms (BoxMap a stop c d))
mouseMove' stop (CalibState ms@(Dragging NW) (BoxMap _ b c d)) =
    mNull (CalibState ms (BoxMap stop b c d))

boxMove' :: Point -> BoxMap -> IO (BoxMap, ())
boxMove' p (BoxMap a b _ d) = return (BoxMap a b p d,())

updatePage :: MVar CalibState -> Bitmap -> Canvas -> Canvas -> CIO ()
updatePage state background can1 can2 = do
  mcalib <- peekMVar state
  let calib = fromMaybe defaultCalibState mcalib

  drawCanvas (box calib) background can2
  drawLines (box calib) can1

drawLines :: BoxMap -> Canvas -> CIO ()
drawLines (BoxMap a b c d) can = do
  render can . lineWidth 1 . stroke $ do
                                   line a b
                                   line b c
                                   line c d
                                   line d a

drawCanvas :: BoxMap -> Bitmap -> Canvas -> CIO ()
drawCanvas box background can = do
  let angle = getAngle box

  render can $ do
    rotate angle $ draw background (0,0)
    color (RGBA 0 0 255 0.5) . font "20px Bitstream Vera" $ do
                                  text (10, 160) $ show (180/pi*angle)
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
