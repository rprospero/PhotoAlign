module Scans (attachScanEvents, initScanState, scanShape, ScanState) where

import Data.IORef
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad (forM)


data Scan = Scan {start :: Point,
                  stop :: Point}

data MouseState = Free | Dragging

data ScanState = ScanState {mouse :: MouseState,
                            scans :: [Scan]}
defaultScanState = ScanState Free []

initScanState = newIORef defaultScanState

makeFree st = st{mouse=Free}

attachScanEvents :: IORef ScanState -> Canvas -> IO () -> IO ()
attachScanEvents scanState can action = do
  onEvent can MouseDown $ mouseDown action scanState
  onEvent can MouseUp $ mouseUp action scanState
  onEvent can MouseMove $ mouseMove action scanState
  return ()

mouseUp :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseUp action state mouse = do
  modifyIORef' state $ makeFree . updateHead mouse
  action

mouseMove :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseMove action state mouse = do
  modifyIORef' state $ updateHead mouse
  action

updateHead :: MouseData -> ScanState -> ScanState
updateHead _ st@(ScanState Free _) = st
updateHead _ st@(ScanState Dragging []) = st
updateHead mouse (ScanState Dragging (s:ss)) =
    ScanState Dragging $ (axisScan (start s) $ floatPair $ mouseCoords mouse):ss

axisScan :: Point -> Point -> Scan
axisScan p p2 = Scan p $ ending p p2
    where
      ending (x1,y1) (x2,y2) =
          if abs (y2 - y1) > abs (x2 - x1)
          then (x1, y2)
          else (x2, y1)

mouseDown :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseDown action state mouse = do
  modifyIORef' state $ \x -> let p = floatPair (mouseCoords mouse)
                            in startDrag p x
  action

startDrag :: Point -> ScanState -> ScanState
startDrag p st = ScanState Dragging $ (Scan p p):scans st


scanShape :: ScanState -> Shape ()
scanShape st = forM (scans st) (\(Scan a b) -> line a b) >> return ()

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)
