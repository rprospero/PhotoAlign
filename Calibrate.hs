{-# LANGUAGE OverloadedStrings #-}

module Calibrate (initCalibState, attachEvents, boxShape, CalibState, getAngle,getScale,alignImage) where

import Data.IORef
import Haste
import Haste.Events
import Haste.Graphics.Canvas
import Haste.JSON
import Data.List (elemIndex)

import JSON

data Corner = NW | NE | SW | SE
            deriving (Show,Eq)
instance JSONable Corner where
    toJSON = Str . toJSString . show
    fromJSON (Str x) = case fromJSStr x of
                         "NW" -> Just NW
                         "SW" -> Just SW
                         "NE" -> Just NE
                         "SE" -> Just SE
                         _ -> Nothing
    fromJSON _ = Nothing

data MouseState = Free | Dragging Corner
                  deriving (Show, Eq)
instance JSONable MouseState where
    toJSON Free = Dict [("state","Free")]
    toJSON (Dragging c) = Dict [("state","Dragging"),
                                ("corner",toJSON c)]
    fromJSON d = do
      state <- d ~> "state"
      case state of
        (Str "Free") -> Just Free
        (Str "Dragging") -> do
                   corner <- d ~> "corner"
                   Dragging <$> fromJSON corner
        _ -> Nothing

data BoxMap = BoxMap Point Point Point Point
              deriving (Eq,Show)
instance JSONable BoxMap where
    toJSON (BoxMap a b c d) = Arr . map toJSON $ [a,b,c,d]
    fromJSON (Arr ps) = let points = map fromJSON ps
                        in BoxMap <$> head points
                               <*> (points !! 1)
                               <*> (points !! 2)
                               <*> (points !! 3)
    fromJSON _ = Nothing


data CalibState = CalibState {mouse ::MouseState,
                              box :: BoxMap}
                  deriving (Eq,Show)
instance JSONable CalibState where
    toJSON calib = Dict [("mouse",toJSON $ mouse calib),
                         ("box",toJSON $ box calib)]
    fromJSON d = CalibState <$> (d ~~> "mouse") <*> (d ~~> "box")

defaultCalibState :: CalibState
defaultCalibState = CalibState Free $ BoxMap (0,0) (0,223) (397,223) (397,0)

initCalibState :: IO (IORef CalibState)
initCalibState = newIORef defaultCalibState

makeFree :: CalibState -> CalibState
makeFree (CalibState _ b) = CalibState Free b


dist :: Point -> Point -> Double
dist (x1,y1) (x2,y2) = (x1-x2)**2+(y1-y2)**2


startDrag :: Point -> CalibState -> CalibState
startDrag p (CalibState _ bx@(BoxMap a b c d)) = CalibState (Dragging corner) bx
    where
      dists = map (dist p) [a,b,c,d]
      corner = case elemIndex (minimum dists) dists of
                     Just 0 -> NW
                     Just 1 -> SW
                     Just 2 -> SE
                     Just 3 -> NE
                     _ -> SE -- Shouldn't happen

attachEvents :: IORef CalibState -> Canvas -> IO () -> IO ()
attachEvents calibState can action = do
  _ <- onEvent can MouseDown $ mouseDown action calibState
  _ <- onEvent can MouseUp $ mouseUp action calibState
  _ <- onEvent can MouseMove $ mouseMove action calibState
  return ()



mouseUp :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseUp action state _ = do
  modifyIORef' state makeFree
  action

mouseDown :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseDown action state m = do
  modifyIORef' state $ \x -> let p = floatPair (mouseCoords m)
                            in startDrag p x
  action

mouseMove :: IO () -> IORef CalibState -> MouseData -> IO ()
mouseMove action state m = do
  modifyIORef' state $ mouseMove' (floatPair $ mouseCoords m)
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


boxShape :: CalibState -> Shape ()
boxShape state =
    let (BoxMap a b c d) = box state
    in path [a, b, c, d, a]

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

-- The shoelace formula for the area of a triangle
shoelace :: Point -> Point -> Point -> Double
shoelace (xa, ya) (xb, yb) (xc, yc) =
    0.5*(xa*yb+xb*yc+xc*ya-xa*yc-xc*yb-xb*ya)

boxArea :: BoxMap -> Double
boxArea (BoxMap a b c d) = shoelace a d c + shoelace d c b

getScale :: Point -> CalibState -> Double
getScale (width,height) state = width*height/boxArea (box state)

getCenter :: CalibState -> Point
getCenter = getCenter' . box

getCenter' :: BoxMap -> Point
getCenter' (BoxMap (xa, ya) (xb, yb) (xc, yc) (xd, yd)) =
    (sum [xa, xb, xc, xd]/4,
     sum [ya, yb, yc, yd]/4)

(><) :: (a -> b) -> (a,a) -> (b,b)
f >< (a,b) = (f a, f b)

alignImage :: Point -> CalibState -> Picture () -> Picture ()
alignImage size st = do
  let angle = getAngle st
      scl = getScale size st
      cen = getCenter st
  translate ((/2) >< size) . scale (sqrt scl, sqrt scl) . rotate (-angle) . translate ((/(-1)) >< cen)
