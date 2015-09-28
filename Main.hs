import Haste
import Haste.App (MonadIO)
import Haste.Concurrent
import Haste.Events
import Haste.Graphics.Canvas

image :: URL
image = "http://imgs.xkcd.com/comics/nasa_press_conference.png"

data MouseState = Free | Dragging Point Point

-- | Then you grab a canvas object...
main :: IO ()
main = concurrent $ do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  mouse <- newMVar Free
  background <- loadBitmap image
  let action = updatePage mouse background can acan
  onEvent can MouseDown $ mouseDown action mouse
  onEvent can MouseUp $ mouseUp action mouse
  onEvent can MouseMove $ mouseMove action mouse
  return ()
  -- onEvent can MouseMove mouseMove
  -- drawCanvas background
  -- animate background acan 2

mouseUp :: CIO () -> MVar MouseState -> MouseData -> CIO ()
mouseUp action state mouse = do
  modifyMVarIO state $ \x -> return (Free,())
  action

mouseDown :: CIO () -> MVar MouseState -> MouseData -> CIO ()
mouseDown action state mouse = do
  modifyMVarIO state $ \x -> let p = floatPair (mouseCoords mouse)
                            in return (Dragging p p,())
  action

mouseMove :: CIO () -> MVar MouseState -> MouseData -> CIO ()
mouseMove action state mouse = do
  modifyMVarIO state $ mouseMove' (floatPair $ mouseCoords mouse)
  action

mouseMove' :: Point -> MouseState -> IO (MouseState, ())
mouseMove' _ Free = return (Free, ())
mouseMove' stop (Dragging start _) = return (Dragging start stop, ())

updatePage :: MVar MouseState -> Bitmap -> Canvas -> Canvas -> CIO ()
updatePage mouse background can1 can2 = do
  drawCanvas mouse background can2
  drawLines mouse can1

drawLines :: MVar MouseState -> Canvas -> CIO ()
drawLines mouse can = do
  m <- peekMVar mouse
  case m of
    Just (Dragging start stop) -> do
                        render can . lineWidth 1 . stroke $ line start stop
                        return ()
    _ -> return ()

drawCanvas :: MVar MouseState -> Bitmap -> Canvas -> CIO ()
drawCanvas mouse background can = do
  m <- peekMVar mouse
  case m of
    Just (Dragging start stop) -> do
           render can $ draw background stop
           return ()
    _ ->
        return ()

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)
