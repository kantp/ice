{-# LANGUAGE DeriveDataTypeable #-}
module Ice.Types

where

import qualified Data.Array.Repa as R
import           Data.Array.Repa.Repr.Vector (V)
import           Data.List (intercalate)
import           Data.Monoid
import           Data.Ord
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word (Word8)
import           System.Console.CmdArgs
-- | Configuration via cmdargs library.
data Config = Config { inputFile :: FilePath
                     , dumpFile :: FilePath
                     , logFile :: FilePath
                     , intName :: String
                     , invariants :: [String]
                     , sortList :: Bool
                     , backsub :: Bool
                     , rMax :: Int
                     , sMax :: Int
                     , visualize :: Bool
                     , failBound :: Double
                     , pipes :: Bool
                     } deriving (Show, Data, Typeable)

-- | A scalar integral is represented by its indices.
newtype SInt = SInt (V.Vector Int) deriving Eq
instance Show SInt where
  show (SInt xs) = "Int[" ++ intercalate "," (map show $ V.toList xs) ++ "]"

-- | Scalar integrals are ordered as in Laporta's paper
-- (arXiv:hep-ph/0102033, Algorithm 1, step 9b), in descending order.
instance Ord SInt where
  compare (SInt x) (SInt y) = laportaOrdering y x where
    laportaOrdering :: V.Vector Int -> V.Vector Int -> Ordering
    laportaOrdering =
      comparing (V.length . V.filter (>0)) -- number of propagators.
      `mappend` comparing (numDots . SInt) -- total number of dots.
      `mappend` comparing (numSPs . SInt) -- total number of scalar products.
      `mappend` compareMissingProps -- comapre which propagators are present/absent.
      `mappend` comparePropPowers -- compare powers of individual propagators.
      `mappend` compareSpPowers -- compare powers of individual scalar products.
    compareMissingProps xs ys = mconcat (zipWith (\ a b -> compare (signum (max a 0)) (signum (max b 0))) (V.toList ys) (V.toList xs))
    comparePropPowers xs ys = mconcat (zipWith (\ a b -> compare (max a 0) (max b 0)) (V.toList xs) (V.toList ys))
    compareSpPowers xs ys = mconcat (zipWith (\ a b -> compare (max (- a) 0) (max (- b) 0)) (V.toList xs) (V.toList ys))

-- | The total number of dots of an integral.
numDots :: SInt -> Int
numDots (SInt xs) = V.sum . V.map (+ (-1)) . V.filter (>0) $ xs

-- | The total number of scalar products of an integral.
numSPs :: SInt -> Int
numSPs (SInt xs) = - (V.sum . V.filter (<0) $ xs)

-- | Check whether an integral has more dots and/or scalar products
-- than allowed.
isBeyond :: Config -> SInt -> Bool
isBeyond c (SInt xs) = r > rMax c || s > sMax c
  where
    r = V.sum . V.map (+ (-1)) . V.filter (>0) $ xs
    s = - (V.sum . V.filter (<0) $ xs)

--  | One term in a polynomial in the kinematic invariants and d
data Term = Term !Integer !(V.Vector Word8) deriving Show
-- | One term in an IBP equation.
data IbpLine = IbpLine { ibpIntegral :: !SInt
                       , ibpCfs :: !(R.Array V R.DIM1 Integer)
                       , ibpExps :: !(R.Array R.U R.DIM2 Word8) } deriving Show
-- | An IBP equation.
newtype Ibp = Ibp (BV.Vector IbpLine) deriving Show

-- | A multivariate Polynomial.
type MPoly = (R.Array V R.DIM1 Integer, R.Array R.U R.DIM2 Word8)
type Equation = BV.Vector (Int, MPoly)

-- | Result of successive Monte Carlo runs.
data TestResult = Unlucky -- ^ We have hit a bad evaluation point and have to discard the result of this run.
                | Restart -- ^ The previous run had a bad evaluation point, and we have to restart.
                | Good !Double -- ^ We have not detected a bad point, and the chance that our result is wrong is less than this.
