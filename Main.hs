import Haste
import Haste.App (MonadIO)
import Haste.Concurrent
import Haste.Events
import Haste.Graphics.Canvas

image :: URL
image = "http://imgs.xkcd.com/comics/nasa_press_conference.png"

-- | Then you grab a canvas object...
main :: IO ()
main = concurrent $ do
  Just can <- getCanvasById "original"
  Just acan <- getCanvasById "aligned"
  rotation <- newMVar 0
  background <- loadBitmap image
  onEvent can Click (const (drawCanvas background acan rotation))
  animate background can rotation
  -- animate background acan 2

drawCanvas :: Bitmap -> Canvas -> MVar Double -> CIO ()
drawCanvas background can mAngle = do
  Just angle <- peekMVar mAngle
  render can $ do
    rotate angle $ draw background (0,0)
    color (RGBA 0 0 255 0.5) . font "20px Bitstream Vera" $ do
      text (10, 160) "You can use transparency too!"
  return ()

-- | ...and use the render function to draw your image.
--   The picture type is a monad, so you can compose several pictures easily
--   using do-notation.
animate :: Bitmap -> Canvas -> MVar Double -> CIO ()
animate background can mAngle = do
  -- There are several transformation functions as well. All of them take a
  -- Picture () as their argument, and apply their transformation only to that
  -- picture, so the user doesn't need to manage the canvas state machine
  -- explicitly.

  modifyMVarIO mAngle $ \angle -> do
                                  return (angle + 0.01,())
  drawCanvas background can mAngle
  setTimer (Once 10) $ animate background can mAngle
  return ()
