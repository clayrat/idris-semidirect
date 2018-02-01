module Util

import Data.Bits
import Data.Fin

import Patricia.IntMap

%access export

lookup' : Bits (S n) -> IntBitMap (S n) v -> Maybe v
lookup' {n} bitKey t = go t where
  go : IntBitMap (S n) v -> Maybe v
  go Empty = Nothing
  go (Leaf treeKey val) = if treeKey == bitKey then Just val else Nothing
  go (Bin pref _ left right) = if bitKey <= pref  -- we can compare `key` with `pref` because of BE patricia trees
                                 then go left
                                 else go right

bitsToHexStr : %static {n : Nat} -> Bits n -> String
bitsToHexStr {n} (MkBits b) with (nextBytes n)
  | Z           = b8ToHexString b
  | S Z         = b16ToHexString b
  | S (S Z)     = b32ToHexString b
  | S (S (S Z)) = b64ToHexString b
  | _ = assert_unreachable

concatMap' : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap' f = foldr ((flip (<+>)) . f) neutral