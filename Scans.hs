module Scans (attachScanEvents, initScanState, scanShape, ScanState,populateTable,dropScan) where

import Data.IORef
import Data.List (delete)
import Haste.DOM
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad (forM,(>=>))

data Scan = Scan {start :: Point,
                  stop :: Point}
            deriving Eq

data MouseState = Free | Dragging

data ScanState = ScanState {mouse :: MouseState,
                            scans :: [Scan]}

defaultScanState :: ScanState
defaultScanState = ScanState Free []

initScanState :: IO (IORef ScanState)
initScanState = newIORef defaultScanState

makeFree :: ScanState -> ScanState
makeFree st = st{mouse=Free}

attachScanEvents :: IORef ScanState -> Canvas -> IO () -> IO ()
attachScanEvents scanState can action = do
  _ <- onEvent can MouseDown $ mouseDown action scanState
  _ <- onEvent can MouseUp $ mouseUp action scanState
  _ <- onEvent can MouseMove $ mouseMove action scanState
  return ()

mouseUp :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseUp action state m = do
  modifyIORef' state $ makeFree . updateHead m
  action

mouseMove :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseMove action state m = do
  modifyIORef' state $ updateHead m
  action

updateHead :: MouseData -> ScanState -> ScanState
updateHead _ st@(ScanState Free _) = st
updateHead _ st@(ScanState Dragging []) = st
updateHead m (ScanState Dragging (s:ss)) =
    ScanState Dragging $ (axisScan (start s) $ floatPair $ mouseCoords m):ss

axisScan :: Point -> Point -> Scan
axisScan p p2 = Scan p $ ending p p2
    where
      ending (x1,y1) (x2,y2) =
          if abs (y2 - y1) > abs (x2 - x1)
          then (x1, y2)
          else (x2, y1)

mouseDown :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseDown action state m = do
  modifyIORef' state $ \x -> let p = floatPair (mouseCoords m)
                            in startDrag p x
  action

startDrag :: Point -> ScanState -> ScanState
startDrag p st = ScanState Dragging $ (Scan p p):scans st


scanShape :: ScanState -> Picture ()
scanShape st = lineWidth 1 . stroke $ forM (scans st) (\(Scan a b) -> line a b) >> return ()

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)

type Killer = Scan -> IO ()

populateTable :: Killer -> ScanState -> Elem -> IO ()
populateTable k st e = do
  clearChildren e
  header <- makeTableHeader
  appendChild e header
  _ <- forM (reverse $ scans st) (makeScanRow k >=> appendChild e)
  return ()

makeTableHeader :: IO Elem
makeTableHeader = makeTableRow ["x1","y1","x2","y2","Delete"]

makeTableRow :: (Show a) => [a] -> IO Elem
makeTableRow xs = do
  texts <- sequence $ map makeTableCell xs
  let cell tx = with (newElem "td") [children [tx]]
  cells <- sequence $ map cell texts
  with (newElem "tr") [children cells]

makeTableCell :: Show a => a -> IO Elem
makeTableCell x = do
  txt <- newTextElem $ show x
  with (newElem "td") [children [txt]]

makeScanRow :: Killer -> Scan -> IO Elem
makeScanRow k sc@(Scan (x1,y1) (x2,y2)) = do
  row <- makeTableRow . map ((/400) . (*25)) $ [x1, y1, x2, y2]
  buttonText <- newTextElem "Delete"
  deleteButton <- with (newElem "button") [children [buttonText]]
  appendChild row deleteButton
  _ <- onEvent deleteButton Click $ const (k sc)
  return row

dropScan :: IO () -> IORef ScanState -> Scan -> IO ()
dropScan action scanState s = do
  modifyIORef' scanState (\x -> x{scans = delete s $scans x})
  action
