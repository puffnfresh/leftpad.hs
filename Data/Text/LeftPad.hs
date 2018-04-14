module Data.Text.LeftPad where

import           Data.Text as T

{-@ measure tlength :: Text -> { n : Int | 0 <= n } @-}
{-@ measure isPrefixOf :: Text -> Text -> Bool @-}
{-@ measure isSuffixOf :: Text -> Text -> Bool @-}
{-@ measure treplicate :: Int -> Text -> Text @-}
{-@ measure tsingleton :: Char -> Text @-}

{-@
assume T.singleton
  :: c : Char
  -> { v : Text | tlength v = 1 && v = tsingleton c }
@-}
{-@
assume T.replicate
  :: n : Int
  -> s : Text
  -> { v : Text | Max (tlength v) 0 (n * tlength s) && v = treplicate n s }
@-}
{-@
assume T.length
  :: s : Text
  -> { v : Int | v = tlength s }
@-}
{-@
assume T.append
  :: a : Text
  -> b : Text
  -> { v : Text | tlength v = tlength a + tlength b && isPrefixOf a v && isSuffixOf b v }
@-}

{-@
leftPad
  :: c : Char
  -> n : Int
  -> s : Text
  -> { v : Text | Max (tlength v) n (tlength s) && isPrefixOf (treplicate (n - tlength s) (tsingleton c)) v && isSuffixOf s v }
@-}
leftPad :: Char -> Int -> Text -> Text
leftPad c n s =
  T.append (T.replicate (n - T.length s) (T.singleton c)) s
