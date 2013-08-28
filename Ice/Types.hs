module Ice.Types

where

import           Data.Monoid
import           Data.Ord
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Control.DeepSeq

-- | A scalar integral is represented by its indices.
newtype SInt = SInt (V.Vector Int) deriving (Show, Eq)

-- | Scalar integrals are ordered as in Laporta's paper.
instance Ord SInt where
  compare (SInt x) (SInt y) = laportaOrdering x y where
    laportaOrdering =
      comparing (V.length . V.filter (/=0))
      `mappend` comparing md
      `mappend` comparing mp
      `mappend` comparing (V.length . V.takeWhile (==0))
      `mappend` comparePropPowers
      `mappend` compareSpPowers
    mp xs = - V.sum (V.filter (<0) xs)
    md xs = let xs' = V.filter (>0) xs
            in V.sum xs' - V.length xs'
    comparePropPowers xs ys = mconcat (zipWith compare (V.toList xs) (V.toList ys))
    scalProds xs = V.toList (V.map negate (V.filter (<0) xs))
    compareSpPowers xs ys =
      mconcat (zipWith compare (scalProds xs) (scalProds ys))

--  | One term in a polynomial in the kinematic invariants and d
data Term = Term !Int !(V.Vector Int) deriving Show
-- | One term in an IBP equation.
data IbpLine = IbpLine { ibpIntegral :: !SInt
                       , ibpCoefficient :: !(BV.Vector Term) } deriving Show
-- | An IBP equation.
data Ibp = Ibp !(BV.Vector IbpLine) deriving Show

instance NFData SInt where
  rnf (SInt x) = rnf x 
instance NFData Term where
  rnf (Term x y) = rnf x `seq` V.map rnf y `seq` ()
instance NFData IbpLine where
  rnf (IbpLine x y) = rnf x `seq` BV.map rnf y `seq` ()
instance NFData Ibp where
  rnf (Ibp x) = rnf x 

