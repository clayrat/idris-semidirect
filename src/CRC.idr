module CRC

import Data.Bits
import Data.Fin
import Data.Primitives.Views

import Patricia.IntMap

import Interfaces
import Util

%access public export

data GF = MkGF (Bits 32)

Eq GF where
  (MkGF a) == (MkGF b) = a == b

Show GF where
  show (MkGF b) = bitsToHexStr b

runGF : GF -> Bits 32
runGF (MkGF b) = b

gf : Integer -> GF
gf i = MkGF $ cast i

zero : GF
zero = gf 0  

poly : Bits 32
poly = cast 0xedb88320 -- -- x^32+x^26+x^23+x^22+x^16+x^12+x^11+x^10+x^8+x^7+x^5+x^4+x^2+x+1

-- | compute x * p(x)
xtimes : GF -> GF
xtimes (MkGF c) = MkGF $ shiftRightLogical c (cast 1) `xor` if getBit 0 c then poly else cast 0

Num GF where
  (MkGF a) + (MkGF b) = MkGF $ a `xor` b
  a * (MkGF b) = if b == cast 0 then zero 
                                else assert_total $ (xtimes a * MkGF (shiftLeft b (cast 1))) + (if getBit 31 b then a else zero)
  fromInteger i with (divides i 2)
    fromInteger (2*_+b) | DivBy _ = if b==1 then gf 0x80000000 else gf 0

x : GF
x = gf 0x40000000 -- x^1

ones : GF
ones = gf 0xffffffff -- | x^31+x^30+...+x+1  

crcs : IntBitMap 8 GF
crcs = fromList $ map (\i => (i, xtimes $ xtimes $ xtimes $ xtimes $ xtimes $ xtimes $ xtimes $ xtimes $ gf i)) [0..255]

data Rem = MkRem GF

Show Rem where
  show (MkRem gf) = show gf

Semigroup Rem where
  (MkRem r1) <+> (MkRem r2) = MkRem (r1 + r2)

Monoid Rem where
  neutral = MkRem 0  

data Dat = MkDat GF

Semigroup Dat where
  (MkDat r1) <+> (MkDat r2) = MkDat (r1 * r2)

Monoid Dat where
  neutral = MkDat 1

Show Dat where
  show (MkDat gf) = show gf

Action Dat Rem where
  act (MkDat d) (MkRem r) = MkRem (d * r)

CRC32 : Type
CRC32 = Semidirect Rem Dat

byte : Bits 8 -> CRC32
byte a = MkSemi (MkRem (fromMaybe x $ lookup' a crcs)) (MkDat x8) -- TODO it's always Just because the table is completely filled
  where x8 = gf 0x800000

runCRC : CRC32 -> Bits 32
runCRC (MkSemi (MkRem p) (MkDat m)) = runGF (ones * m + p + ones)

strCRC : String -> CRC32
strCRC = concatMap' (byte . cast {to=Bits 8} . cast {to=Integer} . ord) . unpack  -- TODO we needs backwards append hence concatMap'
