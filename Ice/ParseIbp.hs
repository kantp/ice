{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

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
import           Data.Int (Int8)
import           Data.Word (Word8)
import           System.IO.Unsafe (unsafePerformIO)

power :: [(Int, B.ByteString)] -> Parser (Int, Word8)
power xs = do
  !coeff <- asum (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  return (coeff, expo)
    where
      stringInd (i,s) = string s *> return i

coefficient :: Parser Integer
coefficient = signed (option 1 decimal) <* option undefined (char '*')

term :: [(Int, B.ByteString)] -> Parser Term
term xs = do
  !cf <- coefficient
  factors <- sepBy' (power xs) (char '*')
  let expos = V.generate (length xs) (\i -> fromMaybe 0 $ lookup i factors)
  return $! Term cf expos

indices :: B.ByteString -> Parser (V.Vector Int8)
indices intName = do
  skipSpace
  string intName
  char '['
  !inds <- liftM V.fromList $ sepBy (signed decimal) (char ',')
  char ']'
  return $! inds

collectTerms :: Int -> [Term] -> MPoly
collectTerms !nVars !ts =
  let !nTerms = length ts
      !cfs = fromListVector (Z :. nTerms) (map (\ (Term x _) -> x) ts)
      !exps = fromUnboxed (Z :. nTerms :. nVars) (V.concat (map (\ (Term _ x) -> x) ts))
  in (cfs, exps)

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

ibp :: B.ByteString -> [(Int, B.ByteString)] -> Parser Ibp
ibp intName xs = do
  !lines <- manyTill' (ibpLine intName xs) (char ';')
  skipSpace
  return $! Ibp (BV.force $ BV.fromList lines)

