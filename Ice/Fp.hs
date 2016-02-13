{-|
Module: Ice.Fp
Description: Implements arithmetic in @F_p@, the field of integers modulo a prime @p@.
Maintainer: philipp.kant7@gmail.com

We keep track of the value of @p@ via reflection, as described in
"Functional Pearl: Implicit Configurations -- or, Type Classes Reflect the Values of Types"
<http://okmij.org/ftp/Haskell/tr-15-04.pdf>

This way, the type system ensures that we never mix up numbers from
different fields @F_p@ and @F_p'@.  It also relieves us from the
burden of passing around the value of @p@ as an additional parameter,
and allows us to write an instance of the 'Num' typeclass for numbers
in @F_p@.

-}

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
import           Data.Int                     (Int64)
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector                  as BV
import qualified Data.Vector.Unboxed          as V
import           Data.Vector.Unboxed.Deriving
import           Data.Word                    (Word8)

-- | Use the reflection package to implement modular arithmetic.  The
-- type @s@ keeps track of the modulus, while @a@ is the actual
-- datatype we want to perform arithmetic with.
newtype Fp s a = Fp a deriving (Show, Eq, Ord)

-- We want to put numbers in F_p in unboxed vectors for efficiency.
-- This template haskell code writes the appropriate instances.
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

-- | After adding or multiplying two numbers, we'll have to take the
-- remainder again to make sure the result is in F_p again.  We could
-- use 'normalise', but if we know that the number we start with is
-- positive, we can use 'rem' instead of 'mod', which is more
-- efficient.  We'll do this often and in inner loops, so it's not a
-- case of premature optimisation.
takeRem :: forall s a . (Reifies s a, Integral a) => a -> Fp s a
{-# INLINE takeRem #-}
takeRem !a = Fp (a `rem` reflect (undefined :: Proxy s))

-- | Determine the modulus used in a calculation.
getModulus :: forall s a . (Reifies s a) => Fp s a -> a
getModulus _ = reflect (undefined :: Proxy s)

instance (Reifies s a, Integral a) => Num (Fp s a) where
  {-# SPECIALIZE instance (Reifies s Int64) => Num (Fp s Int64) #-}
  Fp a + Fp b = takeRem (a + b)
  Fp a * Fp b = takeRem (a * b)
  negate (Fp a) = normalise (negate a)
  fromInteger 0 = Fp 0
  fromInteger 1 = Fp 1
  fromInteger a = Fp (fromInteger $ a `mod` fromIntegral (reflect (undefined :: Proxy s)))
  signum = error "signum in finite field"
  abs = error "abs in finite field"

instance (Reifies s a, Integral a) => Fractional (Fp s a) where
  {-# SPECIALIZE instance (Reifies s Int64) => Fractional (Fp s Int64) #-}
  recip = modInv
  fromRational = error "trying to convert rational to F_p"

-- | Modular inverse, via extended Euclidean algorithm.
modInv :: (Reifies s t, Integral t) => Fp s t -> Fp s t
{-# INLINE modInv #-}
modInv x = let (_, inverse, _) = eea (unFp x) (getModulus x)
           in normalise inverse

-- | Sparse row of a matrix.  First entry of any pair is the column
-- index, snd entry the value.
--
-- We're specialising to @Fp Int64@ below, since that is all we'll use
-- in ICE.
type Row s = V.Vector (Int, Fp s Int64)

-- | Multiplication of a matrix row with a scalar value.
{-# INLINE multRow #-}
multRow :: forall s . Reifies s Int64 => Fp s Int64 -> Row s -> Row s
multRow 0 _ = V.empty
multRow !x !row = V.map (second (*x)) row

-- | Add two matrix rows.
addRows :: Reifies s Int64
          => V.Vector (Int, Fp s Int64)
          -> V.Vector (Int, Fp s Int64)
          -> V.Vector (Int, Fp s Int64)
addRows !r1 !r2 = V.unfoldr step (r1, r2) where
  step (!x, !y)
    | V.null x && V.null y = Nothing -- We're done.
    | V.null x = -- The first row has no more entries, we just need to
                 -- traverse the second row.  Note that the calls to
                 -- unsafeHead and unsafeTail below are all safe,
                 -- since we checked that the vectors are non-empty.
      Just (V.unsafeHead y, (x, V.unsafeTail y))
    | V.null y = -- As above, with first and second row replaced.
      Just (V.unsafeHead x, (V.unsafeTail x, y))
    | otherwise = -- The interesting case: both rows have elements left.
      let (!xi, !xval) = V.unsafeHead x
          (!yi, !yval) = V.unsafeHead y
      in case compare xi yi of
        LT -> Just ((xi, xval), (V.unsafeTail x, y))
        GT -> Just ((yi, yval), (x, V.unsafeTail y))
        EQ -> case xval + yval of
          0 -> step (V.unsafeTail x, V.unsafeTail y)
          val -> Just ((xi, val), (V.unsafeTail x, V.unsafeTail y))

-- | A multivariate polynomial over F_p.  We use a semi-sparse
-- representation.  Only non-zero terms are recorded, but for every
-- non-zero term, all the exponents (even the zeroes) are kept.  This
-- allows bulk evaluation of many polynomials, using the REPA library.
data Poly s = Poly { cfs  :: !(Array U DIM1 (Fp s Int64))
                   -- ^ The non-zero coefficients.
                   , exps :: !(Array U DIM2 Word8)
                   -- ^ The exponents. The first index is aligned with
                   -- @cfs@, the second index enumerates the
                   -- variables.
                   } deriving (Eq, Show)

-- | Evaluation of a multivariate polynomial.
multiEval :: forall s . Reifies s Int64
  => Array U DIM1 (Fp s Int64)
  -> Poly s
  -> Fp s Int64
multiEval !xs !p =
  let (i:._) = extent (exps p)
      xs' = extend (i:.All) xs
      powers = R.zipWith (^) xs' (exps p)
      monomials = R.foldS (*) 1 powers
      terms = R.zipWith (*) (cfs p) monomials
  in foldAllS (+) 0 terms

-- | Evaluate many polynomials simultaneously, calculating the powers only once.
multiEvalBulk :: forall s . Reifies s Int64
  => Array U DIM1 (Fp s Int64)
  -> BV.Vector (Poly s)
  -> V.Vector (Fp s Int64)
multiEvalBulk !xs !ps = V.convert (BV.map evalPoly ps)
  where
    evalPoly :: Poly s -> Fp s Int64
    evalPoly p = let monomials = R.foldS (*) 1 (evalTerms (delay $ exps p))
                     terms = R.zipWith (*) (cfs p) monomials
                 in foldAllS (+) 0 terms
    evalTerms :: Array R.D DIM2 Word8 -> Array R.D DIM2 (Fp s Int64)
    evalTerms ts = R.traverse ts id (\ getElt ix@(Z:._:.i :: DIM2) -> (powers BV.! i) V.! fromIntegral (getElt ix))
    powers = BV.zipWith generatePowers
             (BV.convert (R.toUnboxed (maxPowers (concatTerms (BV.map (R.delay . exps) ps)))))
             (BV.convert (R.toUnboxed xs))
    maxPowers :: Array R.D DIM2 Word8 -> Array U DIM1 Word8
    maxPowers = R.foldS max 0 . R.transpose
    concatTerms :: BV.Vector (Array R.D DIM2 Word8) -> Array R.D DIM2 Word8
    concatTerms =  R.transpose . BV.foldl1' R.append . BV.map R.transpose
    generatePowers :: Word8 -> Fp s Int64 -> V.Vector (Fp s Int64)
    generatePowers n x = V.iterateN (fromIntegral n+1) (*x) 1

-- | Extended Euklid's Algorithm
eea :: (Integral a) => a -> a -> (a,a,a)
{-# INLINE eea #-}
eea !a !b = eea' (abs a) (abs b) 1 0 0 1 where
  eea' !c 0 !c1 !_ !c2 !_ = ( abs c
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
