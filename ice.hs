{-# LANGUAGE BangPatterns #-}
module Main where

import           Control.DeepSeq
import           Control.Exception (bracket)
import           Control.Monad
import           Data.Attoparsec
import qualified Data.ByteString.Char8 as B
import           Data.List
import qualified Data.Map as Map
import qualified Data.Vector as BV
import           Debug.Trace
import           Ice.ParseIbp
import           Ice.Types
import           System.Environment
import           System.IO

refill h = B.hGet h (4*1024)

incrementy xs file h = go 0 [] =<< refill h
 where
   go n !acc is = do
     when (n `mod` 10000 == 0) ( putStr "Parsed equations: "
                                 >> print n)
     r <- parseWith (refill h) (ibp xs) is
     case r of
       Fail _ _ msg -> error msg
       Done bs x
           | B.null bs -> do
              assertNFNamed "parse result" x
              s <- refill h
              if B.null s
                then return $! (x:acc)
                else go (n+1) (x:acc) s
           | otherwise -> assertNFNamed "parse result" x >> go (n+1) (x:acc) bs

getIntegrals :: Ibp -> BV.Vector SInt
getIntegrals (Ibp ibp) = BV.map ibpIntegral ibp

main :: IO ()
main = do
  putStrLn "ice -- the Ibp ChoosEr"
  (eqFile:invariants) <- getArgs
  let invariants' = zip [0..] (map B.pack invariants)
  equations <- withFile eqFile ReadMode $
               incrementy invariants' eqFile
  assertNFNamed "equations" equations
  let integralsUnorder = concatMap (BV.toList . getIntegrals) equations
      integrals = map fst $ (Map.toList . Map.fromList) (zip integralsUnorder (repeat ()))
  putStr "Number of equations: "
  print (length equations)
  putStr "Number of integrals: "
  print (length integrals)
  putStrLn "Integrals: "
  mapM_ print integrals
