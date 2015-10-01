{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module JSON where

import Haste
import Haste.Graphics.Canvas
import Haste.JSON

class JSONable a where
    toJSON :: a -> JSON
    fromJSON :: JSON -> Maybe a

instance JSONable Double where
    toJSON = Num
    fromJSON (Num x) = Just x
    fromJSON _ = Nothing

instance JSONable String where
    toJSON x = Str $ toJSString x
    fromJSON (Str x) = Just $ fromJSStr x
    fromJSON _ = Nothing

instance JSONable a => JSONable [a] where
    toJSON = Arr . map toJSON
    fromJSON (Arr x) = mapM fromJSON x
    fromJSON _ = Nothing

instance JSONable Point where
    toJSON (x,y) = Arr . map toJSON $ [x,y]
    fromJSON (Arr ps) = (,) <$> fromJSON (head ps) <*> fromJSON (ps !! 1)
    fromJSON _ = Nothing

(~~>) :: (JSONable a) => JSON -> JSString -> Maybe a
d ~~> key = do
  v <- d ~> key
  fromJSON v
