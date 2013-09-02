module Ice.Types

where

import           Control.DeepSeq
import qualified Data.Array.Repa as R
import           Data.Int (Int8)
import           Data.List (intercalate)
import           Data.Monoid
import           Data.Ord
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word (Word8)

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
      `mappend` comparing md
      `mappend` comparing mp
      `mappend` comparing (V.length . V.takeWhile (==0))
      `mappend` comparePropPowers
      `mappend` compareSpPowers
    mp xs = - V.sum (V.filter (<0) xs)
    md xs = let xs' = V.filter (>0) xs
            in V.sum xs' - fromIntegral (V.length xs')
    comparePropPowers xs ys = mconcat (zipWith compare (V.toList xs) (V.toList ys))
    scalProds xs = V.toList (V.map negate (V.filter (<0) xs))
    compareSpPowers xs ys =
      mconcat (zipWith compare (scalProds xs) (scalProds ys))

--  | One term in a polynomial in the kinematic invariants and d
data Term = Term !Int !(V.Vector Word8) deriving Show
-- | One term in an IBP equation.
data IbpLine = IbpLine { ibpIntegral :: !SInt
                       , ibpCfs :: !(R.Array R.U R.DIM1 Int)
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

