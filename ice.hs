{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import           Control.Arrow
import           Control.DeepSeq
import           Control.Exception (bracket)
import           Control.Monad
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Attoparsec
import qualified Data.ByteString.Char8 as B
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Numbers.Fp.Fp
import           Data.Numbers.Fp.Matrix
import           Data.Numbers.Fp.Polynomial.Multivariate
import           Data.Numbers.Primes
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Debug.Trace
import           Ice.ParseIbp -- (ibp)
-- import           GHC.AssertNF
import           Ice.Types
import           System.Environment
import           System.IO

refill :: Handle -> IO B.ByteString
refill h = B.hGet h (4*1024)

incrementy :: [(Int, B.ByteString)] -> Handle -> IO [Ibp]
incrementy xs h = go (0 :: Int) [] =<< refill h
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
getIntegrals (Ibp x) = BV.map ibpIntegral x

ibpToRow :: Map.Map SInt Int -> Ibp -> BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Int))
ibpToRow table (Ibp x) = BV.fromList (sortBy (comparing fst) row)
  where
    row = map
          (\ line ->
            ( fromMaybe (error "integral not found.") (Map.lookup (ibpIntegral line) table)
            , (ibpCfs line, ibpExps line))) (BV.toList x)

evalIbps :: forall s . Reifies s Int
            => Int
            -> Array U DIM1 (Fp s Int)
            -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Int))]
            -> Matrix s
evalIbps n xs rs = Matrix { nCols = n, rows = rs' } where
  rs' = BV.fromList (map treatRow rs)
  treatRow r = V.convert $ BV.map (second evalPoly) r
  evalPoly (cs, es) = multiEval xs (Poly (R.computeS $ R.map normalise cs) es)

testMatrix :: forall s . Reifies s Int
              => Int
              -> V.Vector Int
              -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Int))]
              -> (Fp s Int, V.Vector Int, V.Vector Int)
              -- -> (V.Vector Int, V.Vector Int)
testMatrix n xs rs = (d,j,i) where
  (_, d, j, i) = gaussFwd (rows m)
  m = evalIbps n xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
            
withMod :: Int -> (forall s . Reifies s Int => (Fp s Int, V.Vector Int, V.Vector Int))
           -> (Int, V.Vector Int, V.Vector Int)
withMod m x = reify m (\ (_ :: Proxy s) -> (symmetricRep' (x :: (Fp s Int, V.Vector Int, V.Vector Int))))

symmetricRep' (x,y,z) = (symmetricRep x,y,z)

main :: IO ()
main = do
  putStrLn "ice -- the Ibp ChoosEr"
  (eqFile:invariants) <- getArgs
  let invariants' = zip [0..] (map B.pack invariants)
  equations <- withFile eqFile ReadMode $
               incrementy invariants'
  assertNFNamed "equations" equations
  let integralsUnorder = concatMap (BV.toList . getIntegrals) equations
      integrals = map fst $ (Map.toList . Map.fromList) (zip integralsUnorder (repeat ()))
      integralNumbers = Map.fromList (zip integrals [0 :: Int ..])
      ibpRows = map (ibpToRow integralNumbers)  equations
  putStr "Number of equations: "
  print (length equations)
  -- assertNFNamed "equations" equations
  putStr "Number of integrals: "
  print (length integrals)
  -- putStrLn "Integrals: "
  -- mapM_ print (Map.toList integralNumbers)
  -- putStrLn "Equations: "
  -- mapM_ print ibpRows

  let p = 15485867 :: Int -- primes !! 1000000 :: Int
  xs <- V.generateM (length invariants) (\_ -> getRandomR (1,p))
  putStr "Probing for m = "
  print p
  putStr "Random points: "
  print xs
  
  let (d,j,i) = withMod p (testMatrix (length integrals) xs ibpRows)
  putStr "d = "
  print d
  putStr "j = "
  print j
  putStr "i = "
  print i
