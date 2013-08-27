{-# LANGUAGE BangPatterns #-}
module Main where

import           Control.Exception (bracket)
import           Data.Attoparsec
import qualified Data.ByteString.Char8 as B
import           GHC.AssertNF
import           Ice.ParseIbp
import           System.Environment
import           System.IO
refill h = B.hGet h (4*1024)

incrementy xs file h = go [] =<< refill h
 where
   go !acc is = do
     r <- parseWith (refill h) (ibp xs) is
     case r of
       Fail _ _ msg -> error msg
       Done bs x
           | B.null bs -> do
              assertNFNamed "parse result" x
              s <- refill h
              if B.null s
                then return $! (x:acc)
                else go (x:acc) s
           | otherwise -> assertNFNamed "parse result" x >> go (x:acc) bs

main :: IO ()
main = do
  putStrLn "ice"
  (eqFile:invariants) <- getArgs
  let invariants' = zip [0..] (map B.pack invariants)
  equations <- withFile eqFile ReadMode $
               incrementy invariants' eqFile
  print (length equations)
