{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
module Main
       (main)
       where

import           Control.Arrow
import           Control.Exception (assert)
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
import           Data.Time
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
import           Data.Array.Repa.Repr.Vector (V, fromListVector)
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

ibpToRow :: (Map.Map SInt Int, Map.Map SInt Int) -> Ibp -> BV.Vector (Int, (Array V DIM1 Integer, Array U DIM2 Word8))
ibpToRow table (Ibp x) = BV.fromList (sortBy (comparing fst) row)
  where
    row = map
          (\ line ->
            ( fromMaybe (error "integral not found.") (lookupInPair (ibpIntegral line) table)
            , (ibpCfs line, ibpExps line))) (BV.toList x)

unwrapBackGauss :: Int -> (forall s . Reifies s Int => (Fp s Int, [V.Vector Int])) -> [V.Vector Int]
unwrapBackGauss p rs = let (x, res) =  reify p (\ (_ :: Proxy s) -> first symmetricRep (rs :: (Fp s Int, [V.Vector Int])))
                       in res


backGauss :: forall s . Reifies s Int
             => ([V.Vector Int], [Row s])
             -> (Fp s Int, [V.Vector Int])
backGauss (!rsDone, []) = (1, rsDone)
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
    rsDone' = snd normalisedPivotRow:rsDone

evalIbps :: forall s . Reifies s Int
            => Int
            -> Array U DIM1 (Fp s Int)
            -> [BV.Vector (Int, (Array V DIM1 Integer, Array U DIM2 Word8))]
            -> Matrix s
evalIbps n xs rs = Matrix { nCols = n, rows = rs' } where
  rs' = BV.fromList (map treatRow rs)
  treatRow r = V.filter ((/=0) . snd) $ V.convert $ BV.map (second evalPoly) r
  evalPoly (cs, es) = multiEval xs (Poly (R.computeS $ R.map fromInteger cs) es)

testMatrixFwd :: forall s . Reifies s Int
                 => Int
                 -> V.Vector Int
                 -> [BV.Vector (Int, (Array V DIM1 Integer, Array U DIM2 Word8))]
                 -> ([Row s], Fp s Int, V.Vector Int, V.Vector Int)
                 -- -> ([V.Vector Int], Fp s Int, V.Vector Int, V.Vector Int)
                 -- -> (V.Vector Int, V.Vector Int)
testMatrixFwd n xs rs = (rs',d,j,i) where
  (rs', d, j, i) = probeStep ([], BV.toList $ BV.indexed (rows m)) 1 [] []
  m = evalIbps n xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
            
withMod :: Int -> (forall s . Reifies s Int => ([Row s], Fp s Int, V.Vector Int, V.Vector Int))
           -> ([V.Vector (Int, Int)], Int, V.Vector Int, V.Vector Int)
withMod m x = reify m (\ (_ :: Proxy s) -> (symmetricRep' (x :: ([Row s], Fp s Int, V.Vector Int, V.Vector Int))))

symmetricRep' (a,x,y,z) = (map (V.map (second symmetricRep)) a,symmetricRep x,y,z)

config :: Config
config = Config { inputFile = def &= args &= typ "FILE"
                , dumpFile = def &= name "d" &= typFile &= help "File to dump a list of independent equation numbers to."
                , intName = "Int" &= help "Name of the function representing an integral."
                , intNumbers = False &= name "n" &= help "If set, use numbers instead of explicit integrals."
                , invariants = def &= name "i" &= help "Symbols representing kinematic invariants."
                , rMax = def &= help "Maximal number of dots expected to be reduced."
                , sMax = def &= help "Maximal number of scalar products expected to be reduced."
                , backsub = False &= help "Perform backward substitution to investigate which master integrals are needed to express certain integrals."
                , cutseeds = False &= help "Only consider equations that do not involve integrals with more dots/scalar products than given by rMax/sMax."}
         &= summary "ICE -- Integration-By-Parts Chooser of Equations"
         &= details [ "Given a list of Integration-by-parts equations, ICE chooses"
                    , "a maximal linearly independent subset."]
         &= program "ice"

both :: Arrow a => a b' c' -> a (b', b') (c', c')
both f = f *** f

lookupInPair :: Ord k => k -> (Map.Map k a, Map.Map k a) -> Maybe a
lookupInPair k (m1, m2) =
  case Map.lookup k m1 of
    Nothing -> Map.lookup k m2
    x -> x

main :: IO ()
main = do
  c <- cmdArgs config
  let eqFile = inputFile c
      invs = invariants c
  putStrLn "ICE -- Integration-By-Parts Chooser of Equations"
  putStr "Command line arguments: "
  print c
  let invariants' = zip [0..] (map B.pack invs)
  startParseTime <- getCurrentTime
  equations <- liftM reverse $ withFile eqFile ReadMode $
               incrementy (ibpCrusher invariants')
  assertNFNamed "equations" equations
  let (outerIntegrals, innerIntegrals) =
        both (map fst . Map.toList . Map.fromList . (`zip` repeat ()))
        (partition (isBeyond c) (concatMap (BV.toList . getIntegrals) equations))
      nOuterIntegrals = length outerIntegrals
      integrals = uncurry (Data.List.++) (outerIntegrals, innerIntegrals)
      integralNumbers = both Map.fromList
                        ( zip outerIntegrals [0 :: Int ..]
                        , zip innerIntegrals [nOuterIntegrals ..])
      ibpRows = map (ibpToRow integralNumbers)  equations
      ibpRows' = map (BV.map (first (+ (-nOuterIntegrals)))) $ filter ((>= nOuterIntegrals) . BV.minimum . BV.map fst) ibpRows
  putStr "Number of equations: "
  print (length equations)
  -- assertNFNamed "equations" equations
  putStr "Number of integrals: "
  print (length integrals)
  putStrLn (concat ["Number of integrals beyond seed values r="
                   , show (rMax c), " s=", show (sMax c)
                   , ": ", show nOuterIntegrals])
  putStr "Number of integrals within the seed region: "
  print (length innerIntegrals)
  putStr "Number of equations involving no integrals beyond seed values: "
  print $ length ibpRows'

  let p = ((2 :: Int) ^ (31 :: Int))-1
  -- let p = {- 15485867 :: Int -- -} 32416190071 :: Int -- ((2 :: Int) ^ (31 :: Int))-1 -- 15485867 :: Int -- primes !! 1000000 :: Int
  xs <- V.generateM (length invs) (\_ -> getRandomR (1,p))
  putStr "Probing for p = "
  print p
  putStr "Random points: "
  print (V.toList xs)
  startReductionTime <- getCurrentTime
  let (!rs',_,!j,!i) = if cutseeds c
                       then withMod p (testMatrixFwd (length integrals - nOuterIntegrals) xs ibpRows')
                       else withMod p (testMatrixFwd (length integrals) xs ibpRows)
  endReductionTime <- getCurrentTime
  putStr "Number of linearly independent equations: "
  print (V.length i)
  -- putStr "Number of equations that can be dropped : "
  -- print (length equations - V.length i)
  putStrLn "Indices of linearly independent equations (starting at 0):"
  V.mapM_ print i
  printEqnTime <- getCurrentTime

  let (reducibleIntegrals, irreducibleIntegrals) =
        partition (\ (i,_) -> let n = fromMaybe (error  "integral not found.") (lookupInPair i integralNumbers)
                          in V.elem n j) (zip integrals [0 :: Int ..])
  putStrLn "Integrals that can be reduced with these equations:"
  mapM_ print reducibleIntegrals
  putStrLn "Integrals that cannot be reduced with these equations:"
  mapM_ print irreducibleIntegrals
  putStrLn "Possible Master Integrals:"
  mapM_ print (filter ((>= nOuterIntegrals) . snd) irreducibleIntegrals)

  when (backsub c) $ do
    putStrLn "Doing backward substitution."
    let rs'' = unwrapBackGauss p $
               backGauss ([],  map (V.map (second normalise))
                                   ((reverse
                                     . dropWhile ((<nOuterIntegrals) . fst . V.head)
                                     . reverse) rs'))
    putStrLn "Final representations of the integrals will look like:"
    mapM_ (printRow integralNumbers) rs''
  putStr "The probability that this information is wrong is less than "
  print (1 - product [1- (fromIntegral x / fromIntegral p) | x <- [1..V.length i]] :: Double)
  putStrLn "Timings:"
  putStr "Parsing: "
  print $ diffUTCTime startReductionTime startParseTime
  putStr "Solving Equations: "
  print $ diffUTCTime endReductionTime startReductionTime
  putStr "Printing Indices of Equations: "
  print $ diffUTCTime printEqnTime endReductionTime

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
  
