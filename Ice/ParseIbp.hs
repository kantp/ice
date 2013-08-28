{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module Ice.ParseIbp
       (ibp, assertNFNamed)
       where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Data.Attoparsec.Char8
import qualified Data.ByteString as B
import           Data.Maybe
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Debug.Trace
import           Ice.Types
-- import           GHC.AssertNF
import           System.IO.Unsafe (unsafePerformIO)

assertNFNamed :: String -> a -> IO ()
assertNFNamed _ _ = return ()

power :: [(Int, B.ByteString)] -> Parser (Int, Int)
power xs = {-# SCC "power" #-} do
  !coeff <- foldr (<|>) empty (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  option undefined (char '*')
  return $!
    (unsafePerformIO $ assertNFNamed "coeff" coeff)
    `seq`
    (unsafePerformIO $ assertNFNamed "expo" expo)
    `seq`
    (coeff, expo)
    where
      stringInd (i,s) = string s *> return i

coefficient :: Parser Int
coefficient = {-# SCC "coefficient" #-} signed (option 1 decimal) <* option undefined (char '*')

term :: [(Int, B.ByteString)] -> Parser Term
term xs = {-# SCC "term" #-} do
  !cf <- coefficient
  factors <- many' (power xs)
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
  char ' '
  !inds <- liftM V.fromList $ sepBy (signed decimal) (char ' ')
  char ' '
  char '}'
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    inds

ibpLine :: [(Int, B.ByteString)] -> Parser IbpLine
ibpLine xs = {-# SCC "ibpLine" #-} do
  inds <- indices
  char ' '
  char '*'
  char ' '
  poly <- manyTill' (term xs) endOfLine -- (char '\n')
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    (unsafePerformIO $ assertNFNamed "poly" poly)
    `seq`
    IbpLine (SInt inds) (BV.fromList poly)

ibp :: [(Int, B.ByteString)] -> Parser Ibp
ibp xs = do
  !lines <- manyTill' (ibpLine xs) (char ';')
  endOfLine
  return $!
    (unsafePerformIO $ assertNFNamed "lines" lines)
    `seq`
    Ibp (BV.fromList lines)

-- ibps xs = many' $ ibp xs
-- ibps xs = manyTill' (ibp xs) atEnd
