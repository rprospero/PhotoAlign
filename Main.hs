{-# LANGUAGE OverloadedStrings #-}

-- | A program for aligning mounted samples and generating scripts for
-- an x-ray instrument

module Main (main) where

import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.JSON
import Control.Error.Safe (rightMay)
import Control.Monad ((>=>))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT,runMaybeT))
import Data.IORef
import Data.Monoid
import Prelude hiding (head, tail, init, last, read,(!!))
import Safe (readMay,headMay)

import Calibrate
import Scans
import JSON
import Util

data StateDump = StateDump {calib ::CalibState,
                            scandata ::ScanState}
instance JSONable StateDump where
    toJSON s = Dict . zip ["calib","scans"] $ [toJSON $ calib s, toJSON $ scandata s]
    fromJSON d = StateDump <$> (d ~~> "calib") <*> (d ~~> "scans")

-- | Given a file selection element, returns a URL to the selected file
getFilePath :: ElemID -> IO URL
getFilePath = ffi "(function(x){return window.URL.createObjectURL(document.getElementById(x).files[0]);})"

-- | Given a file selection element, get the name of the returned file
getFileName :: ElemID -> IO String
getFileName = ffi "(function(x){return document.getElementById(x).value;})"

-- | Given a file element, reads the file into a text string.  Because
-- of the Javascript callback system, this string must then be passed
-- to an function exported by Haste under the name given in the
-- JSString.
readAsText :: JSString -> ElemID -> IO ()
readAsText = ffi "function(name,x){var r = new FileReader;r.onload=function(q){Haste[name](q.target.result)};r.readAsText(document.getElementById(x).files[0]);}"

-- | The actual Photoalign program
main :: IO ()
main = do
  calibState <- initCalibState
  scanState <- initScanState
  imageName <- newIORef "IndianRoller2.jpg"
  mounts <- elemsByQS document "input[name='mount']"

  let action = updatePage scanState calibState
      contrl = controller action scanState
      triggerController evt x = onEvent x evt $ const contrl
      mainErr = "Page Missing element expected by Main"

  export "processDump" (processDump calibState scanState)

  logMaybeT mainErr $ do
         filePath <- MaybeT $ elemById "filePath"
         loadPath <- MaybeT $ elemById "loadPath"
         _ <- lift $ onEvent filePath Change $ updateBitmap action imageName
         _ <- lift $ onEvent loadPath Change $ const $ readAsText "processDump" "loadPath"
         rots <- MaybeT $ elemById "rotations"
         stepSize <- MaybeT $ elemById "stepSize"


         can <- MaybeT $ elemById "original"
         acan <- MaybeT $ elemById "aligned"
         lift $ attachEvents calibState can action
         -- lift $ attachScanEvents scanState acan action
         upper <- MaybeT $ elemById "top"
         lower <- MaybeT $ elemById "bottom"
         offs <- MaybeT $ elemById "offset"

         lift $ mapM_ (triggerController Change) $ mounts ++ [stepSize,rots, upper, lower, offs]
         lift $ mapM_ (triggerController KeyDown) [stepSize, rots, upper, lower, offs]
  action

-- | Get the value from an element
valueById :: (Read a) => ElemID -> MaybeT IO a
valueById = MaybeT  . elemById >=> flip getProp "value" >=> upgrade . readMay

-- | Read text inpure and update the global variables
controller :: IO () -> IORef ScanState -> IO ()
controller action s = do
  logMaybeT "Could not read rotations" $ do
    r <- valueById "rotations" >>= upgrade . mapM readMay . words
    lift $ modifyIORef' s (\x -> x{rotations=map (*(pi/180)) r})

  logMaybeT "Could not load element step size"$ do
    size <- valueById "stepSize"
    lift $ modifyIORef' s (\x -> x{step=size})

  logMaybeT "Could not read offset elements" $ do
    upper <- valueById "top"
    lower <- valueById "bottom"
    offs <- valueById "offset"
    mount <- elemsByQS document "input[name='mount']:checked" >>= upgrade . headMay
    c <- getProp mount "value" >>= upgrade . readMay

    lift $ modifyIORef' s (\x -> x{top=upper,bottom=lower,offset=offs,choice=c})

  action

-- | Loads a new image file
updateBitmap :: IO ()  -- ^ The generic page update to perform once the
             -> IORef String  -- ^ The IORef which stores the name of the file
             -> ()
             -> IO ()
updateBitmap action nameRef () = do
    img <- getFilePath "filePath"

    setAttrById "originalImage" "xlink:href" img
    setAttrById "alignedImage" "xlink:href" img


    imageName <- Main.getFileName "filePath"
    writeIORef nameRef imageName

    setAttrById "saveLink" "download" $ imageName <> ".json"
    setAttrById "exportLink" "download" $ imageName <> ".txt"

    action

-- | Updates the global state to the values from the JSON file
processDump :: IORef CalibState -- ^ The global state of the calibration
              -> IORef ScanState -- ^ The global state of the scans
              -> JSString -- ^ The text of the JSON file
              -> IO ()
processDump c s result = logMaybeT "failed to decode JSON" $ do
  d <- upgrade $ (rightMay . decodeJSON) result >>= fromJSON
  lift $ writeIORef c $ calib d
  lift $ writeIORef s $ scandata d

updatePage :: IORef ScanState -> IORef CalibState -> IO ()
updatePage scanState calibState = do
  c <- readIORef calibState
  s <- readIORef scanState

  toggleExport s

  let action = updatePage scanState calibState

  fileSave "exportLink" $ toFile s
  fileSave "saveLink" . fromJSStr .  encodeJSON . toJSON $ StateDump c s

  logMaybeT "page missing element for update" $ do
    can1 <- MaybeT $ elemById "original"
    can2 <- MaybeT $ elemById "aligned"
    tbl <- MaybeT $ elemById "scans"

    lift $ populateTable (updateTitle action scanState) (dropScan action scanState) s tbl

    lift $ drawAligned s c can2

toggleExport :: ScanState -> IO ()
toggleExport s = let
    c = if scansReady s
        then ""
        else " disabled"
  in
    setAttrById "exportLink" "class" $ "btn btn-primary" ++ c

drawAligned :: ScanState -> CalibState -> Elem -> IO ()
drawAligned s c can = do
  -- render can $ do
  --   -- alignImage (900,900) c $ scale (0.2,0.2) $ draw rawBackground (0,0)
  --   scanShape s
  alignImage (900,900) c
  return ()

fileSave :: ElemID -> String -> IO()
fileSave e contents = do
  encoded <- encodeURIComponent contents
  let uri = "data:text/plain;charset=utf-8," <> encoded
  setAttrById e "href" uri

upgrade :: (Monad m) => Maybe a -> MaybeT m a
upgrade = MaybeT . return

encodeURIComponent :: String -> IO String
encodeURIComponent = ffi "encodeURIComponent"
