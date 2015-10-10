{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module creates a class for automating the construction and
-- destruction of JSON objects

module JSON where

import Haste
import Haste.Graphics.Canvas
import Haste.JSON
import Prelude hiding (head, tail, init, last, read, (!!))
import Safe (atMay,headMay)

-- | Values which can be converted back and forth from JSON.  The main
-- class laws is that
--
-- > fromJSON . toJSON = id
--
-- Note that that
--
-- > toJSON . fromJSON == id
--
-- does *NOT* hold, as that would imply preserving whitespace and
-- ordering of generic JSON files.
class JSONable a where
    toJSON :: a -> JSON -- ^ Convert the value into JSON
    fromJSON :: JSON -> Maybe a -- ^ Extract a value from JSON or return Nothing on a failure

-- | Turns a Double into a generic JSON number
instance JSONable Double where
    toJSON = Num
    fromJSON (Num x) = Just x
    fromJSON _ = Nothing

-- | Turns a string into a generic JSON number.  Note that it doesn't
-- actually work, since String = [Char], so Haskell can't distinguish
-- from a [Char], even though [Char] is not an instance of JSONable
instance JSONable String where
    toJSON x = Str $ toJSString x
    fromJSON (Str x) = Just $ fromJSStr x
    fromJSON _ = Nothing

-- | Turns a list of JSONable objects into a JSON array
instance JSONable a => JSONable [a] where
    toJSON = Arr . map toJSON
    fromJSON (Arr x) = mapM fromJSON x
    fromJSON _ = Nothing

-- | Turns a Point into a two element JSON array
instance JSONable Point where
    toJSON (x,y) = Arr . map toJSON $ [x,y]
    fromJSON (Arr ps) = (,) <$> (headMay ps >>= fromJSON)
                        <*> (ps `atMay` 1 >>= fromJSON)
    fromJSON _ = Nothing

-- | Pull a value from a JSON object
(~~>) :: (JSONable a) => JSON -> JSString -> Maybe a
d ~~> key = do
  v <- d ~> key
  fromJSON v
