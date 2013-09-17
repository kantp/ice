{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
module Main
       (main)
       where

import Control.Exception (assert)
import           Control.Arrow
import           Control.Monad
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Attoparsec
import qualified Data.ByteString.Char8 as B
import           Data.Function (on)
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Numbers.Fp.Fp
import           Data.Numbers.Fp.Matrix
import           Data.Numbers.Fp.Polynomial.Multivariate
import           System.Console.CmdArgs
-- import           Data.Numbers.Primes
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Ice.ParseCrusher
import           Ice.ParseIbp -- (ibp)
-- import           GHC.AssertNF
import           Data.Word (Word8)
import           Ice.Types
import           System.Environment
import           System.IO
import           System.IO.Unsafe

-- driver for the parser.
refill :: Handle -> IO B.ByteString
refill h = B.hGet h (4*1024)

incrementy :: Parser Ibp -> Handle -> IO [Ibp]
incrementy xs h = go (0 :: Int) [] =<< refill h
 where
   go n !acc is = do
     when (n `mod` 10000 == 0) ( putStr "Parsed equations: "
                                 >> print n)
     r <- parseWith (refill h) xs is
     case r of
       Fail _ _ msg -> error msg
       Done bs x
           | B.null bs -> do
              assertNFNamed "parse result" x
              s <- refill h
              if B.null s
                then return $! (x:acc)
                else go (n+1) (x:acc) s
           | otherwise -> assertNFNamed "parse result" x >> go (n+1) (x:acc) bs

getIntegrals :: Ibp -> BV.Vector SInt
getIntegrals (Ibp x) = BV.map ibpIntegral x

ibpToRow :: (Map.Map SInt Int, Map.Map SInt Int) -> Ibp -> BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))
ibpToRow table (Ibp x) = BV.fromList (sortBy (comparing fst) row)
  where
    row = map
          (\ line ->
            ( fromMaybe (error "integral not found.") (lookupInPair (ibpIntegral line) table)
            , (ibpCfs line, ibpExps line))) (BV.toList x)

probeGauss :: forall s . Reifies s Int
            => BV.Vector (Row s)
            -> ([V.Vector Int], Fp s Int, V.Vector Int, V.Vector Int)
probeGauss !rs = let (fwd, d, j, i) = probeStep ([],  BV.toList $ BV.indexed rs) 1 [] []
                     back = backGauss ([], fwd)
                 in (back, d, j, i)

backGauss :: forall s . Reifies s Int
             => ([V.Vector Int], [Row s])
             -> [V.Vector Int]
backGauss (!rsDone, []) = rsDone
backGauss (!rsDone, !pivotRow:(!rs)) = backGauss (V.map fst pivotRow:rsDone, rs')
  where
    (pivotColumn, invPivot) = second recip (V.head pivotRow)
    rs' = map pivotOperation rs
    pivotOperation row = case V.find ((==pivotColumn) . fst) row of
      Nothing -> row
      Just (_, elt) -> addRows (multRow (-elt*invPivot) pivotRow) row
      
-- | Given a list and an ordering function, this function returns a
-- pair consisting of the minimal element with respect to this
-- ordering, and the rest of the list.
removeMinBy :: (a -> a -> Ordering) -> [a] -> (a, [a])
{-# NOINLINE removeMinBy #-}
removeMinBy cmp xs = foldl' getMin (head xs, []) (tail xs)
  where getMin (!y,!ys) x = case cmp y x of
          GT -> (x, y:ys)
          _  -> (y, x:ys)

-- | This is a variant of 'removeMinBy' that receives an additional
-- equality test function.  It returns a triple of the minimal
-- element, all elements that satisfy the predicate, and the rest.  It
-- is assumed that @eq a b@ and @c LT a@ implies @not (eq c b)@.
removeMinAndSplitBy :: (a -> a -> Ordering) -> (a -> a -> Bool) -> [a] -> (a, [a], [a])
{-# NOINLINE removeMinAndSplitBy #-}
removeMinAndSplitBy cmp eq xs = foldl' getMin (head xs, [], []) (tail xs)
  where getMin (!y,!ys, !zs) x = case cmp y x of
          GT -> if eq x y then (x, y:ys, zs) else (x, [], y: (ys Data.List.++ zs))
          _  -> if eq x y then (y, x:ys, zs) else (y, ys, x:zs)

probeStep :: forall s . Reifies s Int
             => ([Row s], [(Int, Row s)])
             -> Fp s Int
             -> [Int]
             -> [Int]
             -> ([Row s], Fp s Int, V.Vector Int, V.Vector Int)
probeStep (!rsDone, !rs) !d !j !i
  | null rs = (rsDone, d, V.fromList . reverse $ j, V.fromList . reverse $ i)
  | otherwise =
    probeStep (rsDone', rows') d' j' i'
  where
    (pivotRow, rowsToModify, ignoreRows) =
      removeMinAndSplitBy
      (comparing (fst . V.head . snd)
       `mappend` comparing (V.length . snd)
       `mappend` comparing (\ (_,l) -> case V.length l of
                               1 -> 0
                               _ -> - fst (l V.! 1)
                           )
      )
      ((==) `on` (fst. V.head . snd))
      rs
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow
    invPivotElement = recip pivotElement
    normalisedPivotRow = second (multRow invPivotElement) pivotRow
    d' = d * pivotElement
    j' = pivotColumn:j
    pivotOperation (ind, row) =
      let (_,x) = V.head row
      in (ind, addRows (multRow (-x) (V.tail $ snd normalisedPivotRow)) (V.tail row))
    rows' = filter (not . V.null . snd) (fmap pivotOperation rowsToModify) Data.List.++ ignoreRows
    i' = fst pivotRow:i
    rsDone' = (snd normalisedPivotRow:rsDone)




evalIbps :: forall s . Reifies s Int
            => Int
            -> Array U DIM1 (Fp s Int)
            -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))]
            -> Matrix s
evalIbps n xs rs = Matrix { nCols = n, rows = rs' } where
  rs' = BV.fromList (map treatRow rs)
  treatRow r = V.convert $ BV.map (second evalPoly) r
  evalPoly (cs, es) = multiEval xs (Poly (R.computeS $ R.map normalise cs) es)

testMatrix :: forall s . Reifies s Int
              => Int
              -> V.Vector Int
              -> [BV.Vector (Int, (Array U DIM1 Int, Array U DIM2 Word8))]
              -> ([V.Vector Int], Fp s Int, V.Vector Int, V.Vector Int)
              -- -> (V.Vector Int, V.Vector Int)
testMatrix n xs rs = (rs',d,j,i) where
  (rs', d, j, i) = probeGauss (rows m)
  m = evalIbps n xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
            
withMod :: Int -> (forall s . Reifies s Int => ([V.Vector Int], Fp s Int, V.Vector Int, V.Vector Int))
           -> ([V.Vector Int], Int, V.Vector Int, V.Vector Int)
withMod m x = reify m (\ (_ :: Proxy s) -> (symmetricRep' (x :: ([V.Vector Int], Fp s Int, V.Vector Int, V.Vector Int))))

symmetricRep' (a,x,y,z) = (a,symmetricRep x,y,z)




config :: Config
config = Config { inputFile = def &= args &= typ "FILE"
                , dumpFile = def &= name "d" &= typFile &= help "File to dump a list of independent equation numbers to."
                , intName = "Int" &= help "Name of the function representing an integral."
                , intNumbers = False &= name "n" &= help "If set, use numbers instead of explicit integrals."
                , invariants = def &= name "i" &= help "Symbols representing kinematic invariants."
                , rMax = def &= help "Maximal number of dots expected to be reduced."
                , sMax = def &= help "Maximal number of scalar products expected to be reduced."
                , backsub = False &= help "Perform backward substitution to investigate which master integrals are needed to express certain integrals."}
         &= summary "ICE -- Integration-By-Parts Chooser of Equations"


both f = f *** f

-- lookupInPair crit (map1, map2) k
--   | crit k = fromMaybe (error  "integral not found.") (Map.lookup map1 k)
--   | otherwise = Map.size map1 + fromMaybe (error  "integral not found.") (Map.lookup map2 k)

lookupInPair k (m1, m2) =
  case Map.lookup k m1 of
    Nothing -> Map.lookup k m2
    x -> x

main :: IO ()
main = do
  c <- cmdArgs config
  let eqFile = inputFile c
      invs = invariants c

  print c
  
  putStrLn "ice -- the Ibp ChoosEr"
  --   (eqFile:invariants) <- getArgs
  let invariants' = zip [0..] (map B.pack invs)
  equations <- liftM reverse $ withFile eqFile ReadMode $
               incrementy (ibpCrusher invariants')
  assertNFNamed "equations" equations
  let (outerIntegrals, innerIntegrals) = both (map fst . Map.toList . Map.fromList . (`zip` repeat ())) (partition (isBeyond c) (concatMap (BV.toList . getIntegrals) equations))
      integrals = uncurry (Data.List.++) (outerIntegrals, innerIntegrals)
  -- let (outerIntegrals, innerIntegrals) = partition (isBeyond c) (concatMap (BV.toList . getIntegrals) equations)
  --     integrals = map fst $ uncurry (Data.List.++) (both (Map.toList . Map.fromList . (`zip` repeat ())) (outerIntegrals, innerIntegrals))
      integralNumbers = (both Map.fromList) (zip outerIntegrals [0 :: Int ..], zip innerIntegrals [length outerIntegrals ..])
      ibpRows = map (ibpToRow integralNumbers)  equations
  putStr "Number of equations: "
  print (length equations)
  -- assertNFNamed "equations" equations
  putStr "Number of integrals: "
  print (length integrals)
  putStrLn (concat ["Number of integrals beyond seed values r="
                   , show (rMax c), " s=", show (sMax c)
                   , ": ", show (length outerIntegrals)])

  let p = 15485867 :: Int -- 32416190071 :: Int -- ((2 :: Int) ^ (31 :: Int))-1 -- 15485867 :: Int -- primes !! 1000000 :: Int
  xs <- V.generateM (length invs) (\_ -> getRandomR (1,p))
  putStr "Probing for p = "
  print p
  putStr "Random points: "
  print (V.toList xs)
  
  let (rs',d,j,i) = withMod p (testMatrix (length integrals) xs ibpRows)
  putStr "d = "
  print d
  putStr "Number of linearly independent equations: "
  print (V.length i)
  -- putStr "Number of equations that can be dropped : "
  -- print (length equations - V.length i)
  putStrLn "Indices of linearly independent equations (starting at 0):"
  V.mapM_ print i

  let (reducibleIntegrals, irreducibleIntegrals) =
        partition (\ (i,_) -> let n = fromMaybe (error  "integral not found.") (lookupInPair i integralNumbers)
                          in V.elem n j) (zip integrals [0 :: Int ..])
  putStrLn "Integrals that can be reduced with these equations:"
  mapM_ print reducibleIntegrals
  putStrLn "Integrals that cannot be reduced with these equations:"
  mapM_ print irreducibleIntegrals
  -- putStrLn "Sparsity pattern of row reduced form:"
  -- mapM_ (print . V.toList) rs'
  putStrLn "Final representations of the integrals will look like:"
  mapM_ (printRow integralNumbers) rs'
  putStr "The probability that this information is wrong is less than "
  print (1 - product [1- (fromIntegral x / fromIntegral p) | x <- [1..V.length i]] :: Double)
  putStr "Other bound: "
  print (let r = fromIntegral (V.length i)
         in r* (r-1)/ (2 * fromIntegral p) :: Double)
    where printRow intmap r = do
            print r
            putStr $ showIntegral intmap (V.head r)
            putStr " -> {"
            putStr (intercalate ", " (map (showIntegral intmap) (V.toList $ V.tail r)))
            putStrLn "}"
          showIntegral intmap n =
            let (elt, n') = if n < Map.size (fst intmap)
                            then Map.elemAt n (fst intmap)
                            else Map.elemAt (n-Map.size (fst intmap)) (snd intmap)
            in assert (n==n') $ show elt
  
