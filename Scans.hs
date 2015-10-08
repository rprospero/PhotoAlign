{-# LANGUAGE OverloadedStrings #-}


-- | This module handles all of the scans requested by the user
module Scans (attachScanEvents, initScanState, scanShape, ScanState(fileName,rotations), scansReady, populateTable,dropScan,updateTitle,toFile,MouseState) where

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

-- | The complete state of the user's scanning selections
data ScanState = ScanState {mouse :: MouseState, -- ^ whether a new
                                                -- scan is currently
                                                -- being created.
                            scans :: [Scan], -- ^ The scans that the
                                            -- user has requested.
                            fileName :: String, -- ^ The run name for
                                               -- the scans
                            rotations :: [Double]} -- ^ The rotation
                                                  -- angles that we
                                                  -- wish to measure
                 deriving (Eq,Show)
instance JSONable ScanState where
    toJSON s = Dict . zip ["mouse","scans","fileName","rotations"] $ [toJSON $ mouse s,toJSON $ scans s, Str . toJSString $ fileName s,toJSON $ rotations s]
    fromJSON d = ScanState <$> (d ~~> "mouse") <*> (d ~~> "scans") <*> (d ~> "fileName" >>= fromJSONStr)  <*> ((d ~> "rotations") >>= fromJSON)

defaultScanState :: ScanState
defaultScanState = ScanState Free [] "" [15]

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
    | scans st == [] = st
    | otherwise =
        let
          s:ss = scans st
        in
          st{scans= axisScan (start s) (floatPair $ mouseCoords m):ss}

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
  row <- makeTableRow . map ((/900) . (*25)) $ [x1, y1, x2, y2]
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
toFile s = "ccdnewfile " ++
           fileName s ++
           newline ++
           intercalate (newline ++ newline) (map (scanRot s) (rotations s))

scanRot :: ScanState -> Double -> String
scanRot s angle = "umv sar " ++ show (round $ angle*180/pi) ++ newline  ++ (intercalate newline . map (fileLineScan angle) . reverse . scans $ s)

data ScanDir = Horizontal | Vertical

fileLineScan :: Double -> Scan -> String
fileLineScan angle (Scan (x1, y1) (x2, y2) t) =
    let r = rot angle
    in
      if x1 == x2
      then scanCommand Vertical (r $ toMM x1) (toMM y1,toMM y2) t $ getSteps y1 y2
      else scanCommand Horizontal (toMM y1) (r $ toMM x1,r $ toMM x2) t $ getSteps x1 x2

getSteps :: Double -> Double -> Int
getSteps begin end = (round (abs (toMM (end-begin)) / step) :: Int)

-- | Convert pixel coordinates to real ones
toMM :: Double -> Double
toMM x = (x*frameSize/imageSize)
    where
      frameSize = 25 -- The size of the frame in mm
      imageSize = 900 -- The size of the image in pixels

rot :: Double -> Double -> Double
rot angle x = 12.5+(x-12.5)*cos angle

-- | Number of seconds to sleep between runs in a scan
sleep :: String
sleep = "0"

-- | Number of dark runs to perform on each scan.
ndark :: String
ndark = "1"

-- | Size of step between measurements
step :: Double
step = 0.1

scanCommand :: ScanDir -> Double -> (Double,Double) -> String -> Int -> String
scanCommand Vertical x = scanCommand' "sah" x "sav"
scanCommand Horizontal y = scanCommand' "sav" y "sah"

scanCommand' :: String -> Double -> String -> (Double, Double) -> String -> Int -> String
scanCommand' m1 d1 m2 (begin,end) t n =
    let scanString =  intercalate " "
                      ["ccdtrans", m2, show begin, show end,
                       show n,
                       sleep, t, ndark, "1"]
        moveString = "umv " ++ m1 ++ " " ++ show d1
    in
      moveString ++ newline ++ scanString

-- | Determines whether the user has provided enough information to write the script file.
scansReady :: ScanState -> Bool
scansReady s
    | scans s == [] = False
    | (any (invalidTitle) . map title . scans $ s) = False
    | fileName s == "" = False
    | rotations s == [] = False
    | otherwise = True

invalidTitle :: String -> Bool
invalidTitle "" = True
invalidTitle t = any (== ' ') t
