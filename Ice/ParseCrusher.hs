{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module Ice.ParseCrusher
       (ibpCrusher)
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
-- import           GHC.AssertNF
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Int (Int8)
import           Data.Word (Word8)
import           System.IO.Unsafe (unsafePerformIO)

assertNFNamed :: String -> a -> IO ()
{-# INLINE assertNFNamed #-}
assertNFNamed _ _ = return ()

power :: [(Int, B.ByteString)] -> Parser (Int, Word8)
{-# INLINE power #-}
power xs = {-# SCC "power" #-} do
  !coeff <- asum (map stringInd xs)
  expo <- option 1 $ char '^' *> decimal
  return $!
    (unsafePerformIO $ assertNFNamed "coeff" coeff)
    `seq`
    (unsafePerformIO $ assertNFNamed "expo" expo)
    `seq`
    (coeff, expo)
    where
      stringInd (i,s) = string s *> return i

coefficient :: Parser Int
{-# INLINE coefficient #-}
coefficient = {-# SCC "coefficient" #-} signed (option 1 decimal) <* option undefined (char '*')

term :: [(Int, B.ByteString)] -> Parser Term
{-# INLINE term #-}
term xs = {-# SCC "term" #-} do
  !cf <- coefficient
  factors <- sepBy' (power xs) (char '*')
  let expos = V.generate (length xs) (\i -> fromMaybe 0 $ lookup i {- (xs !! i) -} factors)
  return $!
      (unsafePerformIO $ assertNFNamed "cf" cf)
      `seq`
      (unsafePerformIO $ assertNFNamed "expos" expos)
      `seq`
      Term cf expos

indices :: Parser (V.Vector Int8)
{-# INLINE indices #-}
indices = {-# SCC "indices" #-} do
  string "Int["
  !inds <- liftM V.fromList $ sepBy (signed decimal) (char ',')
  char ']'
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    inds

collectTerms :: Int -> [Term] -> (Array U DIM1 Int, Array U DIM2 Word8)
{-# INLINE collectTerms #-}
-- collectTerms [] = (fromUnboxed (Z :. 0) V.empty, fromUnboxed (Z :.0 :. 0) V.empty)
collectTerms !nVars !ts =
  let !nTerms = length ts
      !cfs = fromListUnboxed (Z :. nTerms) (map (\ (Term x _) -> x) ts)
      !exps = fromUnboxed (Z :. nTerms :. nVars) (V.concat (map (\ (Term _ x) -> x) ts))
  in
   (unsafePerformIO $ assertNFNamed "cfArray" cfs)
   `seq`
   (unsafePerformIO $ assertNFNamed "expArray" exps)
   `seq`
   (cfs, exps)

ibpLine :: [(Int, B.ByteString)] -> Parser IbpLine
{-# INLINE ibpLine #-}
ibpLine xs = {-# SCC "ibpLine" #-} do
  inds <- indices
  string "*("
  poly <- manyTill' (term xs) ((char ')') >> endOfLine) -- (char '\n')
  let poly' = collectTerms (length xs) poly
  return $!
    (unsafePerformIO $ assertNFNamed "inds" inds)
    `seq`
    (unsafePerformIO $ assertNFNamed "poly" poly)
    `seq`
    IbpLine (SInt inds) (fst poly') (snd poly') -- (BV.fromList poly)

ibpCrusher :: [(Int, B.ByteString)] -> Parser Ibp
ibpCrusher xs = do
  !lines <- manyTill' (ibpLine xs) (char ';')
  endOfLine
  return $!
    (unsafePerformIO $ assertNFNamed "lines" lines)
    `seq`
    Ibp (BV.force $ BV.fromList lines)

-- ibps xs = many' $ ibp xs
-- ibps xs = manyTill' (ibp xs) atEnd

