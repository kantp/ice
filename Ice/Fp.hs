{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
-- | F_p, the field of integers modulo the prime p.
module Ice.Fp
  ( Fp ()
  , unFp, symmetricRep
  , getModulus
  , normalise
  , Row, multRow, addRows
  , Poly (..), multiEval, multiEvalBulk
  )  where

import           Control.Arrow                (second)
import           Data.Array.Repa              as R
import           Data.Array.Repa.Eval         (Elt)
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector                  as BV
import qualified Data.Vector.Unboxed          as V
import           Data.Vector.Unboxed.Deriving
import           Data.Word                    (Word8)

-- | Use the reflection package to implement modular arithmetic.  The
--   type @s@ keeps track of the modulus, while @a@ is the actual
--   datatype we want to perform arithmetic with.
newtype Fp s a = Fp a deriving (Show, Eq, Ord)

derivingUnbox "Fp"
  [t| forall s a . (V.Unbox a) => Fp s a -> a |]
  [| \(Fp a) -> a |]
  [| \a -> Fp a |]
deriving instance (Elt a) => Elt (Fp s a)

-- | unwrap data from the 'Fp' wrapper.
unFp :: Fp s a -> a
{-# INLINE unFp #-}
unFp (Fp a) = a

-- | Return the symmetric representation of a modular number.
symmetricRep :: (Reifies s a, Integral a) => Fp s a -> a
symmetricRep x
  | x' > halfModulus = x' - modulus
  | x' < - halfModulus = x' + modulus
  | otherwise = x'
  where modulus = getModulus x
        halfModulus = modulus `div` 2
        x' = unFp x

-- | Inject a value into a modular computation.
normalise :: forall s a . (Reifies s a, Integral a) => a -> Fp s a
{-# INLINE normalise #-}
normalise !a = Fp (a `mod` reflect (undefined :: Proxy s))

takeRem :: forall s a . (Reifies s a, Integral a) => a -> Fp s a
{-# INLINE takeRem #-}
takeRem !a = Fp (a `rem` reflect (undefined :: Proxy s))

-- | Determine the modulus used in a calculation.
getModulus :: forall s a . (Reifies s a) => Fp s a -> a
getModulus _ = reflect (undefined :: Proxy s)

instance (Reifies s a, Integral a) => Num (Fp s a) where
  {-# SPECIALIZE instance (Reifies s Int) => Num (Fp s Int) #-}
  Fp a + Fp b = takeRem (a + b)
  Fp a * Fp b = takeRem (a * b)
  negate (Fp a) = normalise (negate a)
  fromInteger 0 = Fp 0
  fromInteger 1 = Fp 1
  fromInteger a = Fp (fromInteger $ a `mod` fromIntegral (reflect (undefined :: Proxy s)))
  signum = error "signum in finite field"
  abs = error "abs in finite field"

instance (Reifies s a, Integral a) => Fractional (Fp s a) where
  {-# SPECIALIZE instance (Reifies s Int) => Fractional (Fp s Int) #-}
  recip = modInv
  fromRational = error "trying to convert rational to F_p"

-- | Modular inverse.
modInv :: (Reifies s t, Integral t) => Fp s t -> Fp s t
modInv x = let (_, inverse, _) = eea (unFp x) (getModulus x)
           in normalise inverse

-- | Sparse row of a matrix.  First entry of any pair is the column
-- index, snd entry the value.
type Row s = V.Vector (Int, Fp s Int)

{-# INLINE multRow #-}
multRow :: forall b d.
                 (Eq b, Num b, V.Unbox b, V.Unbox d) =>
                 b -> V.Vector (d, b) -> V.Vector (d, b)
multRow 0 _ = V.empty
multRow !x !row = V.map (second (*x)) row

{-# INLINE addRows #-}
addRows :: forall a a1.
                 (Eq a1, Num a1, Ord a, V.Unbox a, V.Unbox a1) =>
                 V.Vector (a, a1) -> V.Vector (a, a1) -> V.Vector (a, a1)
addRows !r1 !r2 = V.unfoldr step (r1, r2) where
  step (x, y)
    | V.null x && V.null y = Nothing
    | V.null x = Just (V.head y, (x, V.tail y))
    | V.null y = Just (V.head x, (V.tail x, y))
    | otherwise =
      let (xi, xval) = V.head x
          (yi, yval) = V.head y
      in case compare xi yi of
        LT -> Just ((xi, xval), (V.tail x, y))
        GT -> Just ((yi, yval), (x, V.tail y))
        EQ -> case xval + yval of
          0 -> step (V.tail x, V.tail y)
          val -> Just ((xi, val), (V.tail x, V.tail y))

data Poly s = Poly { cfs  :: !(Array U DIM1 (Fp s Int))
                   , exps :: !(Array U DIM2 Word8) -- ^ exps[(term :. variable)]=exponent
                   } deriving (Eq, Show)

-- | Evaluation of a multivariate polynomial.
multiEval :: forall s . Reifies s Int
  => Array U DIM1 (Fp s Int)
  -> Poly s
  -> Fp s Int
multiEval !xs !p =
  let (i:._) = extent (exps p)
      xs' = extend (i:.All) xs
      powers = R.zipWith (^) xs' (exps p)
      monomials = R.foldS (*) 1 powers
      terms = R.zipWith (*) (cfs p) monomials
  in foldAllS (+) 0 terms

-- | Evaluate many polynomials simultaneously, calculating the powers only once.
multiEvalBulk :: forall s . Reifies s Int
  => Array U DIM1 (Fp s Int)
  -> BV.Vector (Poly s)
  -> V.Vector (Fp s Int)
multiEvalBulk !xs !ps = V.convert (BV.map evalPoly ps)
  where
    evalPoly :: Poly s -> Fp s Int
    evalPoly p = let monomials = R.foldS (*) 1 (evalTerms (delay $ exps p))
                     terms = R.zipWith (*) (cfs p) monomials
                 in foldAllS (+) 0 terms
    evalTerms :: Array R.D DIM2 Word8 -> Array R.D DIM2 (Fp s Int)
    evalTerms ts = R.traverse ts id (\ getElt ix@(Z:._:.i :: DIM2) -> (powers BV.! i) V.! fromIntegral (getElt ix))
    powers = BV.zipWith generatePowers
             (BV.convert (R.toUnboxed (maxPowers (concatTerms (BV.map (R.delay . exps) ps)))))
             (BV.convert (R.toUnboxed xs))
    maxPowers :: Array R.D DIM2 Word8 -> Array U DIM1 Word8
    maxPowers = R.foldS max 0 . R.transpose
    concatTerms :: BV.Vector (Array R.D DIM2 Word8) -> Array R.D DIM2 Word8
    concatTerms =  R.transpose . BV.foldl1' R.append . BV.map R.transpose -- (R.append . R.transpose)
    generatePowers :: Word8 -> Fp s Int -> V.Vector (Fp s Int)
    generatePowers n x = V.iterateN (fromIntegral n+1) (*x) 1

-- | Extended Euklid's Algorithm
eea :: (Integral a) => a -> a -> (a,a,a)
{-# INLINE eea #-}
eea !a !b = eea' (abs a) (abs b) 1 0 0 1 where
  eea' !c !0 !c1 !_ !c2 !_ = ( abs c
                       , c1 `div` (signum a*signum c)
                       , c2 `div` (signum b*signum c) )
  eea' !c !d !c1 !d1 !c2 !d2 =
    let
      q = c `div` d
      r = c - q * d
      r1 = c1 - q * d1
      r2 = c2 - q * d2
    in
     eea' d r d1 r1 d2 r2
