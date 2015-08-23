{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- | F_p, the field of integers modulo the prime p.
module Ice.Fp
  ( Fp, Modulus
  , (+%), (-%), (*%), (/%), (^%), negateMod
  , normalise, modInv
  , Row, multRow, addRows
  , Poly (..), multiEval, multiEvalBulk
  )  where

import           Control.Arrow       (second)
import           Data.Array.Repa     as R
import           Data.List           (foldl')
import qualified Data.Vector         as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word           (Word8)

type Fp = Int
type Modulus = Int

takeRem :: Modulus -> Int -> Fp
{-# INLINE takeRem #-}
takeRem m x = x `rem` m

(+%) :: Modulus -> Fp -> Fp -> Fp
{-# INLINE (+%) #-}
(+%) m x y = takeRem m $ x + y

(-%) :: Modulus -> Fp -> Fp -> Fp
{-# INLINE (-%) #-}
(-%) m x y = takeRem m $ x - y

(*%) :: Modulus -> Fp -> Fp -> Fp
{-# INLINE (*%) #-}
(*%) m x y = takeRem m $ x * y

(/%) :: Modulus -> Fp -> Fp -> Fp
{-# INLINE (/%) #-}
(/%) m x y = (*%) m x $ modInv m y

(^%) :: Modulus -> Fp -> Word8 -> Fp
{-# INLINE (^%) #-}
(^%) m x n = foldl' ((*%) m) 1 $ Prelude.replicate (fromIntegral n) x

negateMod :: Modulus -> Fp -> Fp
{-# INLINE negateMod #-}
negateMod m x = normalise m (-x)

-- | Return the symmetric representation of a modular number.
symmetricRep :: Modulus -> Fp -> Int
symmetricRep m x
  | x > halfModulus = x - m
  | x < - halfModulus = x + m
  | otherwise = x
  where halfModulus = m `div` 2

-- | Inject a value into a modular computation.
normalise :: Modulus -> Int -> Fp
{-# INLINE normalise #-}
normalise m x = x `mod` m

-- | Modular inverse.
modInv :: Modulus -> Fp -> Fp
modInv m x = let (_, inverse, _) = eea x m
             in normalise m inverse

-- | Sparse row of a matrix.  First entry of any pair is the column
-- index, snd entry the value.
type Row = V.Vector (Int, Fp)

{-# INLINE multRow #-}
multRow :: Modulus -> Fp -> Row -> Row
multRow _ 0 _ = V.empty
multRow p !x !row = V.map (second ((*%) p x)) row

{-# INLINE addRows #-}
addRows p !r1 !r2 = V.unfoldr step (r1, r2) where
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
        EQ -> case (+%) p xval yval of
          0 -> step (V.tail x, V.tail y)
          val -> Just ((xi, val), (V.tail x, V.tail y))

data Poly = Poly { cfs  :: !(Array U DIM1 Fp)
                 , exps :: !(Array U DIM2 Word8) -- ^ exps[(term :. variable)]=exponent
                 } deriving (Eq, Show)

-- | Evaluation of a multivariate polynomial.
multiEval
  :: Modulus
  -> Array U DIM1 Fp
  -> Poly
  -> Fp
multiEval m !xs !p =
  let (i:._) = extent (exps p)
      xs' = extend (i:.All) xs
      powers = R.zipWith ((^%) m) xs' (exps p)
      monomials = R.foldS ((*%) m) 1 powers
      terms = R.zipWith ((*%) m) (cfs p) monomials
  in foldAllS ((+%) m) 0 terms

-- | Evaluate many polynomials simultaneously, calculating the powers only once.
multiEvalBulk
  :: Modulus
  -> Array U DIM1 Fp
  -> BV.Vector Poly
  -> V.Vector Fp
multiEvalBulk m !xs !ps = V.convert (BV.map evalPoly ps)
  where
    evalPoly :: Poly -> Fp
    evalPoly p = let monomials = R.foldS ((*%) m) 1 (evalTerms (delay $ exps p))
                     terms = R.zipWith ((*%) m) (cfs p) monomials
                 in foldAllS ((+%) m) 0 terms
    evalTerms :: Array R.D DIM2 Word8 -> Array R.D DIM2 Fp
    evalTerms ts = R.traverse ts id (\ getElt ix@(Z:._:.i :: DIM2) -> (powers BV.! i) V.! fromIntegral (getElt ix))
    powers = BV.zipWith generatePowers
             (BV.convert (R.toUnboxed (maxPowers (concatTerms (BV.map (R.delay . exps) ps)))))
             (BV.convert (R.toUnboxed xs))
    maxPowers :: Array R.D DIM2 Word8 -> Array U DIM1 Word8
    maxPowers = R.foldS max 0 . R.transpose
    concatTerms :: BV.Vector (Array R.D DIM2 Word8) -> Array R.D DIM2 Word8
    concatTerms =  R.transpose . BV.foldl1' R.append . BV.map R.transpose -- (R.append . R.transpose)
    generatePowers :: Word8 -> Fp -> V.Vector Fp
    generatePowers n x = V.iterateN (fromIntegral n+1) ((*%) m x) 1

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
