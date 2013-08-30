{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
module Main
       (main)
       where

import           Control.Arrow
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Attoparsec
import qualified Data.ByteString.Char8 as B
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Numbers.Fp.Fp
import           Data.Numbers.Fp.Matrix
import           Data.Numbers.Fp.Polynomial.Multivariate
import           Data.Numbers.Primes
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Ice.ParseIbp -- (ibp)
-- import           GHC.AssertNF
import           Data.Word (Word8)
import           Ice.Types
import           System.Environment
import           System.IO

-- driver for the parser.
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

ibpToRow :: Map.Map SInt Int -> Ibp -> BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))
ibpToRow table (Ibp x) = BV.fromList (sortBy (comparing fst) row)
  where
    row = map
          (\ line ->
            ( fromMaybe (error "integral not found.") (Map.lookup (ibpIntegral line) table)
            , (ibpCfs line, ibpExps line))) (BV.toList x)




probeGauss :: forall s . Reifies s Int
            => BV.Vector (Row s)
            -> (Fp s Int, V.Vector Int, V.Vector Int)
probeGauss !rs = probeStep (BV.indexed rs) 1 V.empty V.empty

probeStep :: forall s . Reifies s Int
             => BV.Vector (Int, Row s)
             -> Fp s Int
             -> V.Vector Int
             -> V.Vector Int
             -> (Fp s Int, V.Vector Int, V.Vector Int)
probeStep !rs !d !j !i
  | BV.null nonZeroRows = (d, j, i)
  | otherwise = probeStep (BV.force rows') d' j' i'
  where
    nonZeroRows = BV.filter (not . V.null . snd) rs
    pivotRowIndex = BV.minIndexBy
                    (comparing (fst . V.head . snd)
                     `mappend` comparing (V.length . snd))
                    nonZeroRows
    (x,y) = BV.splitAt pivotRowIndex nonZeroRows
    pivotRow = BV.head y
    rowsToModify = x BV.++ BV.tail y
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow
    invPivotElement = recip pivotElement
    normalisedPivotRow = second (multRow invPivotElement) pivotRow
    d' = d * pivotElement
    j' = V.snoc j pivotColumn
    pivotOperation (ind, row) =
      let (n,x) = V.head row
      in (if n == pivotColumn then (ind, addRows (multRow (-x) (snd normalisedPivotRow)) row) else (ind, row))
    rows' = fmap pivotOperation rowsToModify
    i' = V.snoc i (fst pivotRow)




evalIbps :: forall s . Reifies s Int
            => Int
            -> Array U DIM1 (Fp s Int)
            -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))]
            -> Matrix s
evalIbps n xs rs = Matrix { nCols = n, rows = rs' } where
  rs' = BV.fromList (map treatRow rs)
  treatRow r = V.convert $ BV.map (second evalPoly) r
  evalPoly (cs, es) = multiEval xs (Poly (R.computeS $ R.map normalise cs) es)

testMatrix :: forall s . Reifies s Int
              => Int
              -> V.Vector Int
              -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))]
              -> (Fp s Int, V.Vector Int, V.Vector Int)
              -- -> (V.Vector Int, V.Vector Int)
testMatrix n xs rs = (d,j,i) where
  (d, j, i) = probeGauss (rows m)
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
  putStr "Probing for p = "
  print p
  putStr "Random points: "
  print (V.toList xs)
  
  let (d,j,i) = withMod p (testMatrix (length integrals) xs ibpRows)
  putStr "d = "
  print d
  putStr "Number of linearly independent equations: "
  print (V.length i)
  -- putStr "Number of equations that can be dropped : "
  -- print (length equations - V.length i)
  putStrLn "Indices of linearly independent equations (starting at 0):"
  V.mapM_ print i

  let (reducibleIntegrals, irreducibleIntegrals) =
        partition (\ i -> let n = fromMaybe (error  "integral not found.") (Map.lookup i integralNumbers)
                         in V.elem n j) integrals
  putStrLn "Integrals that can be reduced with these equations:"
  mapM_ print reducibleIntegrals
  putStrLn "Integrals that cannot be reduced with these equations:"
  mapM_ print irreducibleIntegrals
  
