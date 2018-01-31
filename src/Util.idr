module Util

import Data.Bits

%access export

bitsToHexStr : %static {n : Nat} -> Bits n -> String
bitsToHexStr {n} (MkBits b) with (nextBytes n)
  | Z           = b8ToHexString b
  | S Z         = b16ToHexString b
  | S (S Z)     = b32ToHexString b
  | S (S (S Z)) = b64ToHexString b
  | _ = assert_unreachable
