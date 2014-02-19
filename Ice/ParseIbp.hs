{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

-- | Attoparsec-based parser for integration-by-parts equations.
module Ice.ParseIbp
       (ibp)
       where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Data.Attoparsec.Char8
import qualified Data.ByteString as B
import           Data.Foldable (asum)
import           Data.Maybe
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Debug.Trace
import           Ice.Types
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Array.Repa.Repr.Vector (V, fromListVector)
import           Data.Word (Word8)
import           System.IO.Unsafe (unsafePerformIO)

-- | Given an association list of invariant names, parse an expression
-- of the form @x^n@ and yield a pair @(i,n)@, where @i@ is the key of
-- @x@ in the association list.  If the exponent is missing, it is
-- treated as @1@.
power :: [(Int, B.ByteString)] -> Parser (Int, Word8)
power xs = do
  !coeff <- asum (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  return (coeff, expo)
    where
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
      !cfs = fromListVector (Z :. nTerms) (map (\ (Term x _) -> x) ts)
      !exps = fromUnboxed (Z :. nTerms :. nVars) (V.concat (map (\ (Term _ x) -> x) ts))
  in (cfs, exps)

-- | Parse one line containing one integral and a polynomial that is
-- the coefficient of this integral in the equation.
ibpLine :: B.ByteString -> [(Int, B.ByteString)] -> Parser IbpLine
ibpLine intName xs = do
  inds <- indices intName
  skipSpace
  char '*'
  skipSpace
  char '('
  skipSpace
  poly <- manyTill' (term xs) (skipSpace >> char ')' >> endOfLine) -- (char '\n')
  let poly' = collectTerms (length xs) poly
  return $ uncurry (IbpLine (SInt inds)) poly'

-- | Parse one equation.  An equation consists of one or more
-- 'ibpLine's, terminated by a semicolon (on a separate line).
ibp :: B.ByteString -> [(Int, B.ByteString)] -> Parser Ibp
ibp intName xs = do
  !lines <- manyTill' (ibpLine intName xs) (char ';')
  skipSpace
  return $! Ibp (BV.force $ BV.fromList lines)

