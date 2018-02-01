module Main

import Data.Bits 

import CRC
import Util

main : IO ()
main = printLn $ bitsToHexStr $ runCRC $ strCRC "The quick brown fox jumps over the lazy dog"
