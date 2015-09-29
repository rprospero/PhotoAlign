module Calibrate (initCalibState, attachEvents, boxShape, CalibState, getAngle) where

import Data.IORef
import Haste.Events
import Haste.Graphics.Canvas
import Haste.DOM
import Data.List (elemIndex,minimum)

data Corner = NW | NE | SW | SE
data MouseState = Free | Dragging Corner
data BoxMap = BoxMap Point Point Point Point

data CalibState = CalibState {mouse ::MouseState,
                              box :: BoxMap}
defaultCalibState = CalibState Free $ BoxMap (0,0) (0,50) (50,50) (50,0)

initCalibState = newIORef defaultCalibState

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

attachEvents :: IORef CalibState -> Canvas -> IO () -> IO ()
attachEvents calibState can action = do
  onEvent can MouseDown $ mouseDown action calibState
  onEvent can MouseUp $ mouseUp action calibState
  onEvent can MouseMove $ mouseMove action calibState
  return ()



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


floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)


boxMove' :: Point -> BoxMap -> IO (BoxMap, ())
boxMove' p (BoxMap a b _ d) = return (BoxMap a b p d,())

boxShape :: CalibState -> Shape ()
boxShape state =
    let (BoxMap a b c d) = box state
    in do line a b
          line b c
          line c d
          line d a

getAngle :: CalibState -> Double
getAngle = getAngle' . box

getAngle' :: BoxMap -> Double
getAngle' (BoxMap a b c d) = atan $ (s1+s2+s3+s4)/4
    where
      s1 = tan $ slope a b-pi/2
      s2 = tan $ slope b c
      s3 = tan $ slope c d+pi/2
      s4 = tan $ slope d a-pi

slope :: Point -> Point -> Double
slope (x1,y1) (x2,y2) = atan2 (y2-y1) (x2-x1)
