{-# LANGUAGE OverloadedStrings #-}

module Scans (attachScanEvents, initScanState, scanShape, ScanState,populateTable,dropScan,toFile,MouseState) where

import Data.IORef
import Data.List (delete,intercalate)
import Haste
import Haste.DOM
import Haste.JSON
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad (forM,(>=>))

import JSON

data Scan = Scan {start :: Point,
                  stop :: Point}
            deriving (Show, Eq)
instance JSONable Scan where
    toJSON s = Arr . map toJSON $ [start s,stop s]
    fromJSON (Arr ss) = Scan <$> fromJSON (ss !! 0) <*> fromJSON (ss !! 1)
    fromJSON _ = Nothing

data MouseState = Free | Dragging
                  deriving (Show,Eq)
instance JSONable MouseState where
    toJSON = Str . toJSString . show
    fromJSON (Str x) = case fromJSStr x of
                         "Dragging" -> Just Dragging
                         "Free" -> Just Free
                         _ -> Nothing
    fromJSON _ = Nothing

data ScanState = ScanState {mouse :: MouseState,
                            scans :: [Scan]}
                 deriving (Eq,Show)
instance JSONable ScanState where
    toJSON s = Dict . zip ["mouse","scans"] $ [toJSON $ mouse s,toJSON $ scans s]
    fromJSON d = ScanState <$> (d ~~> "mouse") <*> (d ~~> "scans")

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
makeTableHeader = do
  hs <- mapM makeTableHeader' ["x1","y1","x2","y2","Delete"]
  newElem "tr" `with` [children hs]

makeTableHeader' :: String -> IO Elem
makeTableHeader' x = do
    txt <- newTextElem x
    newElem "th" `with` [children [txt]]

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
  deleteButton <- makeDeleteButton
  appendChild row deleteButton
  _ <- onEvent deleteButton Click $ const (k sc)
  return row

makeDeleteButton :: IO Elem
makeDeleteButton = do
  icon <- newElem "span" `with` [attr "class" =: "glyphicon glyphicon-remove"]
  button <- newElem "button" `with` [attr "class" =: "btn btn-danger",
                                    children [icon]]
  return button

dropScan :: IO () -> IORef ScanState -> Scan -> IO ()
dropScan action scanState s = do
  modifyIORef' scanState (\x -> x{scans = delete s $scans x})
  action

toFile :: ScanState -> String
toFile = intercalate "\n" . map fileLineScan . reverse . scans

fileLineScan :: Scan -> String
fileLineScan (Scan (x1, y1) (x2, y2)) = intercalate "\t" . map show $ map ((* 25) . (/ 400)) [x1,y1,x2,y2]
