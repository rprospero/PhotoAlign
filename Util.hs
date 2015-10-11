module Util (setAttrById, logMaybeT) where

import Haste.DOM
import Control.Monad.Trans.Maybe (MaybeT(MaybeT,runMaybeT))

logMaybeT :: String -> MaybeT IO () -> IO ()
logMaybeT err x = do
    val <- runMaybeT x
    case val of
      Just _ -> return ()
      Nothing -> print err >> return ()

setAttrById :: ElemID -> PropID -> String -> IO ()
setAttrById e p v =
    let
        err = "Failed to set " ++ p ++ "on page element " ++ e
    in logMaybeT err $ do
      el <- MaybeT $  elemById e
      setAttr el p v
