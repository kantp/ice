{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
-- | Attoparsec-based parser for integration-by-parts equations.
--
-- We can either parse polynomials to a sparse representation, or
-- evaluate them on the fly.  The latter is done unless multiple
-- evaluations are needed, in order to save memory.
module Ice.ParseIbp
       (ibp, evaldIbp)
       where

import           Control.Monad
import           Data.Array.Repa hiding (map)
import           Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString as B
import           Data.Foldable (asum)
import           Data.List (foldl')
import           Data.Maybe
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word (Word8)
import           Ice.Fp
import           Ice.Types

-- | Given an association list of invariant names, parse an expression
-- of the form @x^n@ and yield a pair @(i,n)@, where @i@ is the key of
-- @x@ in the association list.  If the exponent is missing, it is
-- treated as @1@.
power :: [(Int, B.ByteString)] -> Parser (Int, Word8)
power xs = do
  !coeff <- asum (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  return (coeff, expo)

evaldPower :: Reifies s Int => [(Fp s Int, B.ByteString)] -> Parser (Fp s Int)
evaldPower xs = do
  coeff <- asum (map stringInd xs)
  expo <- option 1 $ char '^' *> (decimal :: Parser Int)
  return (coeff^expo)

stringInd :: (a, B.ByteString) -> Parser a
stringInd (i,s) = string s *> return i

-- | Parse a coefficient, which may or may not contain a sign and an
-- integer.  A missing integer is treated as @1@.  The multiplication
-- sign between the numeric coefficient and powers of variables is
-- also consumed.
coefficient :: Parser Integer
coefficient = signed (option 1 decimal) <* option undefined (char '*')

-- | Parse a term, i.e. a 'coefficient' times zero or more 'power's.
term :: [(Int, B.ByteString)] -> Parser Term
term xs = do
  !cf <- coefficient
  factors <- sepBy' (power xs) (char '*')
  let expos = V.generate (length xs) (\i -> fromMaybe 0 $ lookup i factors)
  return $! Term cf expos

evaldTerm :: Reifies s Int => [(Fp s Int, B.ByteString)] -> Parser (Fp s Int)
evaldTerm xs = do
  cf <- coefficient
  factors <- sepBy' (evaldPower xs) (char '*')
  return (foldl' (*) (fromInteger cf) factors)

-- | Parse the indices of an integral.  For example,
-- @indices \"Int\" \"Int[1,1,2,0]\"@ would yield @[1,1,2,0]@.
indices :: B.ByteString -> Parser (V.Vector Int)
indices intName = do
  skipSpace
  string intName
  char '['
  !inds <- liftM V.fromList $ sepBy' (signed decimal) (char ',')
  char ']'
  return $! inds

-- | Transform a list of Terms, as parsed by 'term', into a
-- multivariate polynomial of type 'MPoly'.
collectTerms :: Int -> [Term] -> MPoly
collectTerms !nVars !ts =
  let !nTerms = length ts
      !cfs = BV.force $ BV.fromList [ x | (Term x _) <- ts]
      !exps = fromUnboxed (Z :. nTerms :. nVars) (V.concat (map (\ (Term _ x) -> x) ts))
  in MPoly (cfs, exps)

-- | Parse one line containing one integral and a polynomial that is
-- the coefficient of this integral in the equation.
ibpLine :: B.ByteString -> [(Int, B.ByteString)] -> Parser (IbpLine MPoly)
ibpLine intName xs = do
  inds <- indices intName
  skipSpace
  char '*'
  skipSpace
  char '('
  skipSpace
  poly <- manyTill' (term xs) (skipSpace >> char ')' >> endOfLine) -- (char '\n')
  let poly' = collectTerms (length xs) poly
  return $ IbpLine (SInt inds) poly'

evaldIbpLine :: Reifies s Int => B.ByteString -> [(Fp s Int, B.ByteString)] -> Parser (IbpLine (Fp s Int))
evaldIbpLine intName xs = do
  inds <- indices intName
  skipSpace
  char '*'
  skipSpace
  char '('
  skipSpace
  poly <- manyTill' (evaldTerm xs) (skipSpace >> char ')' >> endOfLine) -- (char '\n')
  let poly' = foldl' (+) 0 poly
  return $ IbpLine (SInt inds) poly'

-- | Parse one equation.  An equation consists of one or more
-- 'ibpLine's, terminated by a semicolon (on a separate line).
ibp :: B.ByteString -> [(Int, B.ByteString)] -> Parser (Ibp MPoly)
ibp intName xs = do
  !lines <- manyTill' (ibpLine intName xs) (char ';')
  skipSpace
  return $! Ibp (BV.force $ BV.fromList lines)

evaldIbp :: Reifies s Int => B.ByteString -> [(Fp s Int, B.ByteString)] -> Parser (Ibp (Fp s Int))
evaldIbp intName xs = do
  !lines <- manyTill' (evaldIbpLine intName xs) (char ';')
  skipSpace
  return $! Ibp (BV.force $ BV.fromList lines)

