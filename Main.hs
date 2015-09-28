import Haste
import Haste.App (MonadIO)
import Haste.Concurrent
import Haste.Events
import Haste.Graphics.Canvas
import Data.Maybe (fromMaybe)

image :: URL
image = "http://imgs.xkcd.com/comics/nasa_press_conference.png"

data MouseState = Free | Dragging Point Point
data BoxMap = BoxMap Point Point Point Point

data CalibState = CalibState {mouse ::MouseState,
                              box :: BoxMap}
defaultCalibState = CalibState Free $ BoxMap (0,0) (0,50) (50,50) (50,0)

makeFree :: CalibState -> CalibState
makeFree (CalibState _ b) = CalibState Free b
startDrag :: Point -> CalibState -> CalibState
startDrag p (CalibState _ b) = CalibState (Dragging p p) b



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
mouseMove' stop (CalibState (Dragging start _) (BoxMap a b _ d)) =
    mNull (CalibState (Dragging start stop)
                      (BoxMap a b stop d))

boxMove' :: Point -> BoxMap -> IO (BoxMap, ())
boxMove' p (BoxMap a b _ d) = return (BoxMap a b p d,())

updatePage :: MVar CalibState -> Bitmap -> Canvas -> Canvas -> CIO ()
updatePage state background can1 can2 = do
  mcalib <- peekMVar state
  let calib = fromMaybe defaultCalibState mcalib

  drawCanvas (mouse calib) background can2
  drawLines (box calib) can1

drawLines :: BoxMap -> Canvas -> CIO ()
drawLines (BoxMap a b c d) can = do
  render can . lineWidth 1 . stroke $ do
                                   line a b
                                   line b c
                                   line c d
                                   line d a

drawCanvas :: MouseState -> Bitmap -> Canvas -> CIO ()
drawCanvas (Dragging start stop) background can = do
  render can $ draw background stop
  return ()
drawCanvas Free _ _ = return ()

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)
