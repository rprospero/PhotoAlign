{-# LANGUAGE OverloadedStrings #-}

module Scans (attachScanEvents, initScanState, scanShape, ScanState, scansReady, populateTable,dropScan,updateTitle,toFile,MouseState) where

import Data.IORef
import Data.List (delete,intercalate)
import Haste
import Haste.DOM
import Haste.JSON
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad (forM,forM_,(>=>))

import JSON

data Scan = Scan {start :: Point,
                  stop :: Point,
                  title :: String}
            deriving (Show, Eq)
instance JSONable Scan where
    toJSON s = Dict [("title",Str . toJSString$ title s),
                    ("points",Arr . map toJSON $ [start s,stop s])]
    fromJSON d@(Dict _) = Scan <$> (getJArr d "points" >>= (fromJSON . head))<*>((getJArr d "points") >>= (fromJSON . (!! 1))) <*> ((d ~> "title") >>= fromJSONStr)
    fromJSON _ = Nothing

fromJSONStr :: JSON -> Maybe String
fromJSONStr (Str x) = Just (toString x)
fromJSONStr _ = Nothing

getJArr :: JSON -> JSString -> Maybe [JSON]
getJArr d k = case d ~> k of
                Nothing -> Nothing
                Just (Arr x) -> Just x
                Just _ -> Nothing

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
    ScanState Dragging $ axisScan (start s) (floatPair $ mouseCoords m):ss

axisScan :: Point -> Point -> Scan
axisScan p p2 = Scan p (ending p p2) ""
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
startDrag p st = ScanState Dragging $ Scan p p "":scans st


scanShape :: ScanState -> Picture ()
scanShape st = lineWidth 1 . stroke $ forM_ (scans st) (\(Scan a b _) -> line a b)

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)

type Killer = Scan -> IO ()

type Changer = Elem -> Scan -> IO ()

populateTable :: Changer -> Killer -> ScanState -> Elem -> IO ()
populateTable c k st e = do
  clearChildren e
  header <- makeTableHeader
  appendChild e header
  _ <- forM (reverse $ scans st) (makeScanRow c k >=> appendChild e)
  return ()

makeTableHeader :: IO Elem
makeTableHeader = do
  hs <- mapM makeTableHeader' ["x1","y1","x2","y2","title","Delete"]
  newElem "tr" `with` [children hs]

makeTableHeader' :: String -> IO Elem
makeTableHeader' x = do
    txt <- newTextElem x
    newElem "th" `with` [children [txt]]

makeTableRow :: (Show a) => [a] -> IO Elem
makeTableRow xs = do
  texts <- mapM makeTableCell xs
  let cell tx = with (newElem "td") [children [tx]]
  cells <- mapM cell texts
  with (newElem "tr") [children cells]

makeTableCell :: Show a => a -> IO Elem
makeTableCell x = do
  txt <- newTextElem $ show x
  with (newElem "td") [children [txt]]

makeScanRow :: Changer -> Killer -> Scan -> IO Elem
makeScanRow c k sc@(Scan (x1,y1) (x2,y2) t) = do
  row <- makeTableRow . map ((/400) . (*25)) $ [x1, y1, x2, y2]
  titleLabel <- makeTitleLabel t
  deleteButton <- makeDeleteButton
  appendChild row =<< inCell titleLabel
  appendChild row deleteButton
  _ <- onEvent deleteButton Click $ const (k sc)
  _ <- onEvent titleLabel Change $ const (c titleLabel sc)
  return row

inCell :: Elem -> IO Elem
inCell t = newElem "td" `with` [children [t]]

makeTitleLabel :: String -> IO Elem
makeTitleLabel s = do
  newElem "input" `with` [attr "type" =: "text",
                          attr "value" =: s]

makeDeleteButton :: IO Elem
makeDeleteButton = do
  icon <- newElem "span" `with` [attr "class" =: "glyphicon glyphicon-remove"]
  newElem "button" `with` [attr "class" =: "btn btn-danger",
                           children [icon]]

dropScan :: IO () -> IORef ScanState -> Killer
dropScan action scanState s = do
  modifyIORef' scanState (\x -> x{scans = delete s $scans x})
  action

updateTitle :: IO () -> IORef ScanState -> Changer
updateTitle action scanState label scan = do
  l <- getProp label "value"
  modifyIORef' scanState (fixScanState scan (\x -> x{title=l}))
  action

when :: (a -> Bool) -> (a->a) -> [a] -> [a]
when _ _ [] = []
when test f (x:xs) = if test x
                     then f x:when test f xs
                     else x:when test f xs

fixScanState :: Scan -> (Scan->Scan) -> ScanState -> ScanState
fixScanState scan f s =
    let ss = scans s
    in s{scans=when (==scan) f ss}

toFile :: ScanState -> String
toFile = intercalate "\r\n" . map fileLineScan . reverse . scans

data ScanDir = Horizontal | Vertical

fileLineScan :: Scan -> String
fileLineScan (Scan (x1, y1) (x2, y2) t) =
    if x1 == x2
    then scanCommand Vertical (toMM x1) (toMM y1,toMM y2) t
    else scanCommand Horizontal (toMM y1) (toMM x1,toMM x2) t

-- | Convert pixel coordinates to real ones
toMM :: Double -> Double
toMM x = (x*frameSize/imageSize)
    where
      frameSize = 25 -- | The size of the frame in mm
      imageSize = 400 -- | The size of the image in pixels

-- | Number of seconds to sleep between runs in a scan
sleep :: String
sleep = "0"

-- | Number of dark runs to perform on each scan.
ndark :: String
ndark = "1"

-- | Size of step between measurements
step :: Double
step = 0.1

scanCommand :: ScanDir -> Double -> (Double,Double) -> String -> String
scanCommand Vertical x p t = scanCommand' "sah" x "sav" p t
scanCommand Horizontal y p t = scanCommand' "sav" y "sah" p t

scanCommand' :: String -> Double -> String -> (Double, Double) -> String -> String
scanCommand' m1 d1 m2 (begin,end) t =
    let scanString =  intercalate " "
                      ["ccdtrans", m2, show begin, show end,
                       show $ (floor (abs (end-begin) / step) :: Int),
                       sleep, t, ndark, "1"]
        moveString = "umv " ++ m1 ++ " " ++ show d1
    in
      moveString ++ "\r\n" ++ scanString


scansReady :: ScanState -> Bool
scansReady s =
    let ss = scans s
    in case ss of
         [] -> False
         xs -> all (validTitle) . map title $ xs

validTitle :: String -> Bool
validTitle "" = False
validTitle t = all (/= ' ') t
