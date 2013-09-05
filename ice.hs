{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
module Main
       (main)
       where

import           Control.Arrow
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
-- import           Data.Numbers.Primes
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Ice.ParseIbp (ibp)
import           GHC.AssertNF
import           Data.Word (Word8)
import           Ice.Types
import           System.Environment
import           System.IO
import           System.IO.Unsafe

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

-- | During Gaussian elimination, we want to keep the rows ordered.  First criterium is the column index of the first non-zero entry.  Next is the number of non-zero entries.  Otherwise, lines are compared by the rest of the column indices, with the original row number as tie-braker..
-- lineKey :: (Int, Row s) -> (Int, Int)
-- lineKey (i, x)
--   | V.null x = (0,0)
--   | otherwise = (fst (V.head x),i)
lineKey :: (Int, Row s) -> [Int]
lineKey (i, x)
  | V.null x = []
  | otherwise = fst (V.head x): V.length x: V.toList (V.snoc (V.map fst (V.tail x)) i)

probeGauss :: forall s . Reifies s Int
            => BV.Vector (Row s)
            -> (Fp s Int, V.Vector Int, V.Vector Int)
probeGauss !rs = probeStep (BV.toList $ BV.indexed rs) 1 [] []
-- probeGauss rs = probeStep' (Map.fromList $ map (\ x -> (lineKey x, x)) (BV.toList $ BV.indexed rs)) 1 [] []

-- probeStep' :: forall s . Reifies s Int
--               => Map.Map (Int, Int) (Int, Row s)
--               -> Fp s Int
--               -> [Int]
--               -> [Int]
--               -> (Fp s Int, V.Vector Int, V.Vector Int)
-- {-# NOINLINE probeStep' #-}
-- probeStep' !rs !d !j !i
--   | Map.null rs = (d, V.fromList . reverse $ j, V.fromList . reverse $ i)
--   | otherwise =
--     -- unsafePerformIO (assertNFNamed "rs" rs'')
--     -- `seq`
--     -- unsafePerformIO (assertNFNamed "d" d')
--     -- `seq`
--     -- unsafePerformIO (assertNFNamed "j" j')
--     -- `seq`
--     -- unsafePerformIO (assertNFNamed "i" i')
--     -- `seq`
--     probeStep' rs'' d' j' i'
--   where
--     ((pivotKey, (pivotIndex, pivotRow)), rs') = Map.deleteFindMin rs
--     (modRows, ignoreRows) = Map.partitionWithKey (\ k _ -> k > (1 + fst pivotKey,0)) rs'
--     -- (modRows, ignoreRows) = Map.partitionWithKey (\ k _ -> k > [head pivotKey + 1]) rs'
--     (pivotColumn, pivotElement) = V.head pivotRow
--     normalisedPivotRow = multRow (recip pivotElement) pivotRow
--     d' = d * pivotElement
--     j' = pivotColumn:j
--     i' = pivotIndex:i
--     pivotOperation :: (Int, Row s) -> (Int, Row s)
--     pivotOperation (ind, row) =
--       let (_,x) = V.head row
--       in (ind, addRows (multRow (-x) normalisedPivotRow) row)
--     newRows = filter (not . V.null . snd) (map (pivotOperation . snd) (Map.toList modRows))
--     rs'' = Map.fromList (map (\ x -> (lineKey x, x)) newRows) `Map.union` ignoreRows


probeStep :: forall s . Reifies s Int
             => [(Int, Row s)]
             -> Fp s Int
             -> [Int]
             -> [Int]
             -> (Fp s Int, V.Vector Int, V.Vector Int)
probeStep !rs !d !j !i
-- probeStep rs d j i
  | null rs = (d, V.fromList . reverse $ j, V.fromList . reverse $ i)
  | otherwise =
    -- unsafePerformIO (assertNFNamed "rows" rows')
    -- `seq`
    -- unsafePerformIO (assertNFNamed "d" d')
    -- `seq`
    -- unsafePerformIO (assertNFNamed "j" j')
    -- `seq`
    -- unsafePerformIO (assertNFNamed "i" i')
    -- `seq`
    probeStep rows' d' j' i'
  where
    pivotRowIndex = fst $ minimumBy -- (comparing (lineKey . snd))
                    (comparing (fst . V.head . snd . snd)
                     `mappend` comparing (V.length . snd . snd)
                     `mappend` comparing (\ (_,(_,l)) -> case V.length l of
                                             1 -> 0
                                             _ -> - fst (l V.! 1)
                                         )
                    )
                    (zip [0..] rs)
                    
    (rows1, rows2) = splitAt pivotRowIndex rs
    pivotRow = head rows2
    rowsToModify = rows1 Data.List.++ tail rows2
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow
    invPivotElement = recip pivotElement
    normalisedPivotRow = second (multRow invPivotElement . V.tail) pivotRow
    d' = d * pivotElement
    j' = pivotColumn:j
    pivotOperation (ind, row) =
      let (n,x) = V.head row
      in (if n == pivotColumn then (ind, addRows (multRow (-x) (snd normalisedPivotRow)) (V.tail row)) else (ind, row))
    rows' = filter (not . V.null . snd) . fmap pivotOperation  $ rowsToModify
    i' = fst pivotRow:i




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
  equations <- liftM reverse $ withFile eqFile ReadMode $
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

  let p = 15485867 :: Int -- 32416190071 :: Int -- ((2 :: Int) ^ (31 :: Int))-1 -- 15485867 :: Int -- primes !! 1000000 :: Int
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
  putStr "The probability that this information is wrong is less than "
  print (product [1- (fromIntegral x / fromIntegral p) | x <- [1..V.length i]] :: Double)
  putStr "Other bound: "
  print (let r = fromIntegral (V.length i)
         in r* (r-1)/ (2 * fromIntegral p) :: Double)
  
