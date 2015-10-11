{-# LANGUAGE OverloadedStrings #-}


-- | This module handles all of the scans requested by the user
module Scans (attachScanEvents, initScanState, scanShape,
              ScanState(step,rotations,top,bottom,offset,choice),
              scansReady, populateTable,dropScan,updateTitle,toFile,MouseState) where

import Data.IORef
import Data.List (delete,intercalate)
import Haste
import Haste.DOM
import Haste.JSON
import Haste.Events
import Haste.Graphics.Canvas
import Control.Monad (forM,forM_,(>=>))
import Text.Printf
import Prelude hiding (head, tail, init, last, read,(!!))
import Safe (headMay,atMay)

import JSON

data Scan = Scan {start :: Point,
                  stop :: Point,
                  title :: String}
            deriving (Show, Eq)
instance JSONable Scan where
    toJSON s = Dict [("title",Str . toJSString$ title s),
                    ("points",Arr . map toJSON $ [start s,stop s])]
    fromJSON d@(Dict _) = Scan <$> (getJArr d "points" >>= headMay >>= fromJSON)<*>(getJArr d "points" >>= flip atMay 1 >>= fromJSON) <*> ((d ~> "title") >>= fromJSONStr)
    fromJSON _ = Nothing

fromJSONStr :: JSON -> Maybe String
fromJSONStr (Str x) = Just (toString x)
fromJSONStr _ = Nothing

getJArr :: JSON -> JSString -> Maybe [JSON]
getJArr d k = case d ~> k of
                Nothing -> Nothing
                Just (Arr x) -> Just x
                Just _ -> Nothing

-- | Whether the user is currently performing a drag or leaving the mouse free
data MouseState = Free | Dragging
                  deriving (Show,Eq)
instance JSONable MouseState where
    toJSON = Str . toJSString . show
    fromJSON (Str x) = case fromJSStr x of
                         "Dragging" -> Just Dragging
                         "Free" -> Just Free
                         _ -> Nothing
    fromJSON _ = Nothing

data Frame = Top | Bottom
             deriving (Eq, Show, Read)
instance JSONable Frame where
    toJSON =Str . toJSString .show
    fromJSON (Str x) = case fromJSStr x of
                         "Top" -> Just Top
                         "Bottom" -> Just Bottom
                         _ -> Nothing
    fromJSON _ = Nothing

-- | The complete state of the user's scanning selections
data ScanState = ScanState {mouse :: MouseState, -- ^ whether a new
                                                -- scan is currently
                                                -- being created.
                            scans :: [Scan], -- ^ The scans that the
                                            -- user has requested.
                            top :: Double, -- ^ The Y offset of the
                                          -- upper frame
                            bottom :: Double, -- ^ The Y offset of the
                                             -- lower frame
                            offset :: Double, -- ^ The X offset of the
                                             -- frames
                            choice :: Frame, -- ^ Which frame position
                                            -- holds the sample.
                            step :: Double, -- ^ The Scan step size in mm
                            rotations :: [Double]} -- ^ The rotation
                                                  -- angles that we
                                                  -- wish to measure
                 deriving (Eq,Show)
instance JSONable ScanState where
    toJSON s = Dict . zip ["mouse","scans","top","bottom","offset","choice","step","rotations"] $ [toJSON $ mouse s,toJSON $ scans s, toJSON $ top s, toJSON $ bottom s, toJSON $ offset s, toJSON $ choice s, toJSON $ step s, toJSON $ rotations s]
    fromJSON d = ScanState <$> (d ~~> "mouse")
                 <*> (d ~~> "scans")
                 <*> ((d ~> "top") >>= fromJSON)
                 <*> ((d ~> "bottom") >>= fromJSON)
                 <*> ((d ~> "offset") >>= fromJSON)
                 <*> ((d ~> "choice") >>= fromJSON)
                 <*> defaultStep d
                 <*> ((d ~> "rotations") >>= fromJSON)

defaultStep :: JSON -> Maybe Double
defaultStep d =
    case d ~> "step" of
      Just x -> fromJSON x
      Nothing -> Just 0.1 -- Default step size from V0.1

defaultScanState :: ScanState
defaultScanState = ScanState Free [] 0 50 0 Top 0.5 (map (*(pi/180)) [0,5..50])

-- | Creates a reference to a set of scans
initScanState :: IO (IORef ScanState)
initScanState = newIORef defaultScanState

makeFree :: ScanState -> ScanState
makeFree st = st{mouse=Free}

-- | Registers actions on the scan canvas
attachScanEvents :: IORef ScanState -- ^ A reference to the global
                                   -- state of the scan
                 -> Canvas -- ^ The canvas being registered
                 -> IO () -- ^ A generic update to perform after any event
                 -> IO ()
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
updateHead m st
    | mouse st == Free = st
    | null (scans st) = st
    | otherwise =
        let
          s:ss = scans st
        in
          st{scans= axisScan (start s) (floatPair $ mouseCoords m):ss}

axisScan :: Point -> Point -> Scan
axisScan p p2 = Scan p (ending p p2) ""
    where
      ending (xa,ya) (xb,yb) =
          if abs (yb - ya) > abs (xb - xa)
          then (xa, yb)
          else (xb, ya)

mouseDown :: IO () -> IORef ScanState -> MouseData -> IO ()
mouseDown action state m = do
  modifyIORef' state $ \x -> let p = floatPair (mouseCoords m)
                            in startDrag p x
  action

startDrag :: Point -> ScanState -> ScanState
startDrag p st = st{mouse=Dragging,scans=Scan p p "":scans st}

-- | Returns a picture with the scans coloured Magenta
scanShape :: ScanState -> Picture ()
scanShape st = lineWidth 1 . color (RGB 255 0 255) . stroke $ forM_ (scans st) (\(Scan a b _) -> line a b)

floatPair :: (Int, Int) -> Point
floatPair (x,y) = (fromIntegral x, fromIntegral y)

type Killer = Scan -> IO ()

type Changer = Elem -> Scan -> IO ()

-- | Add a table to the HTML document which contains the scans
populateTable :: Changer -- ^ An action which updates the a scan title
                        -- in the global state with the value in an
                        -- element
              -> Killer -- ^ An action which removes a scan from the
                       -- global state
              -> ScanState -- ^ The current state of the scan
              -> Elem -- ^ where to place the table
              -> IO ()
populateTable c k st e = do
  clearChildren e
  header <- makeTableHeader
  appendChild e header
  _ <- forM (reverse $ scans st) (makeScanRow c k st >=> appendChild e)
  return ()

makeTableHeader :: IO Elem
makeTableHeader = do
  hs <- mapM makeTableHeader' ["x1","y1","x2","y2","frames","time (minutes)","title","Delete"]
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

makeScanRow :: Changer -> Killer -> ScanState -> Scan -> IO Elem
makeScanRow c k st sc@(Scan (xa, ya) (xb, yb) t) = do
  let toReal = (/900) . (*25)
  row <- makeTableRow [toReal xa, toReal ya, toReal xb, toReal yb,
                      fromIntegral $ getFrameCount (step st) sc,
                      fromIntegral . round . (*(fromIntegral . length $ rotations st)) . (*(3.5/60)) . fromIntegral
                                      . getFrameCount (step st) $ sc]
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
makeTitleLabel s = newElem "input" `with` [attr "type" =: "text",
                                           attr "value" =: s]

makeDeleteButton :: IO Elem
makeDeleteButton = do
  icon <- newElem "span" `with` [attr "class" =: "glyphicon glyphicon-remove"]
  newElem "button" `with` [attr "class" =: "btn btn-danger",
                           children [icon]]

-- | Given a generic continuation action and a reference to the global
-- scan state, creates a function which will remove a given scan from
-- the state and perform the update continuation.
dropScan :: IO () -> IORef ScanState -> Killer
dropScan action scanState s = do
  modifyIORef' scanState (\x -> x{scans = delete s $scans x})
  action

-- | Given a generic continuation action and a reference to the global
-- scan state, creates a function which will update any chosen scan
-- with the value of a form element
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

newline :: String
newline = "\r\n"

-- | Turns a ScanState into a script macro for SPEC
toFile :: ScanState -> String
toFile s = intercalate (newline ++ newline) (map (scanRot s) (rotations s))

scanRot :: ScanState -> Double -> String
scanRot s angle = "umv sar " ++ show (round $ angle*180/pi) ++ newline  ++ (intercalate newline . map (fileLineScan s angle) . reverse . scans $ s)

data ScanDir = Horizontal | Vertical

fileLineScan :: ScanState -> Double -> Scan -> String
fileLineScan s angle sc@(Scan (xa, _) (xb, _) _)
    | xa == xb = scanCommand Vertical s sc angle
    | otherwise = scanCommand Horizontal s sc angle

getFrameCount :: Double -> Scan -> Int
getFrameCount stepSize (Scan (xa, ya) (xb, yb) _)
    | xa == xa = getSteps stepSize ya yb
    | otherwise = getSteps stepSize xa xb

getSteps :: Double -> Double -> Double -> Int
getSteps stepSize begin end = round (abs (toMM (end-begin)) / stepSize ) :: Int

-- | Convert pixel coordinates to real ones
toMM :: Double -> Double
toMM x = x*frameSize/imageSize
    where
      frameSize = 25 -- The size of the frame in mm
      imageSize = 900 -- The size of the image in pixels

-- | Number of seconds to sleep between runs in a scan
sleep :: Double
sleep = 0

-- | Number of dark runs to perform on each scan.
ndark :: Int
ndark = 1

-- | Exposure time
time :: Double
time = 0.04

x1 :: ScanState -> Scan -> Double -> Double
x1 s (Scan (x,_) _ _) angle = offset s + 12.5 + (toMM x-12.5)* cos angle
x2 :: ScanState -> Scan -> Double -> Double
x2 s (Scan _ (x,_) _) angle = offset s + 12.5 + (toMM x-12.5)* cos angle
y1 :: ScanState -> Scan -> Double
y1 s (Scan (_,y) _ _) = case choice s of
                          Top -> top s + toMM y
                          Bottom -> bottom s + toMM y
y2 :: ScanState -> Scan -> Double
y2 s (Scan _ (_,y) _)  =case choice s of
                          Top -> top s + toMM y
                          Bottom -> bottom s + toMM y
z1 :: ScanState -> Scan -> Double -> Double
z1 _ (Scan (x,_) _ _) angle = (toMM x-12.5)* sin angle
z2 :: ScanState -> Scan -> Double -> Double
z2 _ (Scan _ (x,_) _) angle = (toMM x-12.5)* sin angle

showDouble :: Double -> String
showDouble = printf "%.3f"

scanCommand :: ScanDir -> ScanState -> Scan -> Double -> String
scanCommand Vertical s scan angle =
    let moveString = "umv sah " ++ showDouble (x1 s scan angle) ++ " tmp2 " ++ showDouble (z1 s scan angle)
        scanString = unwords
                     ["ccdtrans sav", showDouble $ y1 s scan, showDouble $ y2 s scan,
                      show $ getFrameCount (step s) scan, show time, show sleep, "\"" ++ title scan ++ "\"",
                      show ndark, "1"]
    in moveString ++ newline ++ scanString
scanCommand Horizontal s scan angle =
    let moveString = "umv sav " ++ showDouble (y1 s scan)
        begin = x1 s scan angle
        end = x2 s scan angle
        zbegin = z1 s scan angle
        zend = z2 s scan angle
        n = getFrameCount (step s) scan
        scanString = "for(i=0;i<=" ++ show n ++ ";i+=1)" ++ newline
                     ++ "{" ++ newline
                     ++ "  y = " ++ showDouble begin ++ "+i*"
                     ++ showDouble ((end-begin)/fromIntegral n) ++ newline
                     ++ "  x = " ++ showDouble zbegin ++ "+i*"
                     ++ showDouble ((zend-zbegin)/fromIntegral n) ++ newline
                     ++ "  umv sah y"  ++ newline
                     ++ "  umv tmp2 x" ++ newline
                     ++ unwords ["  ccdacq_nodark",show time,"\"" ++ title scan ++ "\""] ++ newline
                     ++ "}" ++ newline
    in moveString ++ newline ++ scanString

-- | Determines whether the user has provided enough information to write the script file.
scansReady :: ScanState -> Bool
scansReady s
    | null (scans s) = False
    | any invalidTitle . map title . scans $ s = False
    | null (rotations s) = False
    | otherwise = True

invalidTitle :: String -> Bool
invalidTitle "" = True
invalidTitle t = ' ' `elem` t
