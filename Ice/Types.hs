{-# LANGUAGE DeriveDataTypeable #-}
module Ice.Types

where

import           Control.DeepSeq
import qualified Data.Array.Repa as R
import           Data.Array.Repa.Repr.Vector (V)
import           Data.Int (Int8)
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
                     , intName :: String
                     , invariants :: [String]
                     , backsub :: Bool
                     , rMax :: Int8
                     , sMax :: Int8
                     } deriving (Show, Data, Typeable)

-- | A scalar integral is represented by its indices.
newtype SInt = SInt (V.Vector Int8) deriving Eq
instance Show SInt where
  show (SInt xs) = "I(" ++ intercalate "," (map show $ V.toList xs) ++ ")"

-- | Scalar integrals are ordered as in Laporta's paper, in decreasing order.
instance Ord SInt where
  compare (SInt x) (SInt y) = laportaOrdering y x where
    laportaOrdering :: V.Vector Int8 -> V.Vector Int8 -> Ordering
    laportaOrdering =
      comparing (V.length . V.filter (/=0))
      `mappend` comparing (numDots . SInt)
      `mappend` comparing (numSPs . SInt)
      `mappend` comparing (V.length . V.takeWhile (==0))
      `mappend` comparePropPowers
      `mappend` compareSpPowers
    comparePropPowers xs ys = mconcat (zipWith (\ a b -> compare (max a 0) (max b 0)) (V.toList xs) (V.toList ys))
    compareSpPowers xs ys = mconcat (zipWith (\ a b -> compare (max (- a) 0) (max (- b) 0)) (V.toList xs) (V.toList ys))

numDots :: SInt -> Int8
numDots (SInt xs) = V.sum . V.map (+ (-1)) . V.filter (>0) $ xs

numSPs :: SInt -> Int8
numSPs (SInt xs) = - (V.sum . V.filter (<0) $ xs)

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

instance NFData SInt where
  rnf (SInt x) = rnf x 
instance NFData Term where
  rnf (Term x y) = rnf x `seq` V.map rnf y `seq` ()
instance NFData IbpLine where
  rnf (IbpLine x y z) =
    rnf x
    `seq` (R.computeS (R.map rnf y) :: R.Array R.U R.DIM1 ())
    `seq` (R.computeS (R.map rnf z) :: R.Array R.U R.DIM2 ())
    `seq` ()
instance NFData Ibp where
  rnf (Ibp x) = rnf x 

