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
import           Data.Maybe
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           GHC.AssertNF
import           System.IO.Unsafe (unsafePerformIO)

data Term = Term !Int !(V.Vector Int) deriving Show
data Line = Line !(V.Vector Int) !(BV.Vector Term) deriving Show
data Ibp = Ibp !(BV.Vector Line) deriving Show

instance NFData Term where
  rnf (Term x y) = x `seq` y `deepseq` () --  V.force y `seq` ()
instance NFData Line where
  rnf (Line x y) = x `deepseq` y `deepseq` () --  BV.force (BV.map deepseq y) `seq` ()

power :: [(Int, B.ByteString)] -> Parser (Int, Int)
power xs = {-# SCC "power" #-} do
  coeff <- msum (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  option undefined (char '*')
  return $! (coeff, expo)
    where
      stringInd (i,s) = string s *> return i

coefficient :: Parser Int
coefficient = {-# SCC "coefficient" #-} signed (option 1 decimal) <* option undefined (char '*')

term :: [(Int, B.ByteString)] -> Parser Term
term xs = {-# SCC "term" #-} do
  !cf <- coefficient
  factors <- many (power xs)
  let expos = V.generate (length xs) (\i -> fromMaybe 0 $ lookup i {- (xs !! i) -} factors)
  return $!
      (unsafePerformIO $ assertNFNamed "cf" cf)
      `seq`
      (unsafePerformIO $ assertNFNamed "expos" expos)
      `seq`
      Term cf expos

indices :: Parser (V.Vector Int)
indices = {-# SCC "indices" #-} do
  char '{'
  skipSpace
  !inds <- liftM V.fromList $ sepBy (signed decimal) (char ' ')
  skipSpace
  char '}'
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    inds

-- ibpLine :: [(Int, B.ByteString)] -> Parser (V.Vector Int, [Term])
ibpLine :: [(Int, B.ByteString)] -> Parser Line
ibpLine xs = {-# SCC "ibpLine" #-} do
  inds <- indices
  skipSpace
  char '*'
  skipSpace
  poly <- manyTill' (term xs) (char '\n')
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    (unsafePerformIO $ assertNFNamed "poly" poly)
    `seq`
    Line inds (BV.fromList poly)

-- ibp :: [(Int, B.ByteString)] -> Parser [(V.Vector Int, [Term])]
ibp :: [(Int, B.ByteString)] -> Parser Ibp
-- ibp xs = {-# SCC "ibp" #-} (liftM $ Ibp . BV.fromList) (skipSpace *> manyTill (ibpLine xs) (char ';') <* endOfLine)

ibp xs = do
  skipSpace
  lines <- manyTill' (ibpLine xs) (char ';')
  endOfLine
  lines `deepseq` return $!
    (unsafePerformIO $ assertNFNamed "lines" lines)
    `seq`
    Ibp (BV.fromList lines)

-- ibps xs = many' $ ibp xs
-- ibps xs = manyTill' (ibp xs) atEnd
