{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification#-}
module Ice.Types

where

import           Control.Monad.RWS
import qualified Data.Array.Repa as R
import           Data.List (intercalate)
import qualified Data.Map.Strict as Map
import           Data.Monoid
import           Data.Ord
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word (Word8)
import           Ice.Fp
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

data StateData = StateData { system :: LinSystem
                           , integralMaps :: (Map.Map SInt (), Map.Map SInt ())
                           , nIntegrals :: Int
                           } deriving Show

-- | State Monad of Ice.
type IceMonad a = RWST Config String StateData IO a

data LinSystem = PolynomialSystem [Equation MPoly]
               | FpSystem { p :: Int
                          , as :: V.Vector Int
                          , mijs :: [Equation Int] }
               | FpSolved { image :: [(V.Vector (Int, Int))]
                          , rowNumbers :: V.Vector Int
                          , pivotColumnNumbers :: V.Vector Int} deriving Show

nEq :: LinSystem -> Int
nEq (PolynomialSystem xs) = length xs
nEq (FpSystem _ _ xs) = length xs

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
data IbpLine a = IbpLine !SInt !a deriving (Show, Functor)
-- data IbpLine = IbpLine { ibpIntegral :: !SInt
--                        , ibpCfs :: !(BV.Vector Integer)
--                        , ibpExps :: !(R.Array R.U R.DIM2 Word8) } deriving Show
-- | An IBP equation.
newtype Ibp a = Ibp (BV.Vector (IbpLine a)) deriving (Show, Functor)

-- | A multivariate Polynomial.
type MPoly = (BV.Vector Integer, R.Array R.U R.DIM2 Word8)

-- | Dummy 'Num' instance for 'MPoly'.  We only need (primitive) addition.
instance Num MPoly where
  (+) (!x1,!y1) (!x2,!y2) =
    ( BV.force $ x1 BV.++ x2, R.computeS $ R.transpose (R.transpose y1 R.++ R.transpose y2))
  (*) =         error "(*) not implemented for multivariate polynomials."
  signum =      error "signum not implemented for multivariate polynomials."
  fromInteger = error "fromInteger not implemented for multivariate polynomials."
  abs =         error "abs not implemented for multivariate polynomials."

type Equation a = BV.Vector (Int, a)

-- | Result of successive Monte Carlo runs.
data TestResult = Unlucky -- ^ We have hit a bad evaluation point and have to discard the result of this run.
                | Restart -- ^ The previous run had a bad evaluation point, and we have to restart.
                | Good !Double -- ^ We have not detected a bad point, and the chance that our result is wrong is less than this.



