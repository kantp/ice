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
import           Ice.Fp
import           Data.Time
import           System.Console.CmdArgs
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Ice.ParseIbp
import           Data.Array.Repa.Repr.Vector (V)
import           Data.Word (Word8)
import           Ice.Types
import           System.IO

-- driver for the parser.
refill :: Handle -> IO B.ByteString
refill h = B.hGet h (4*1024)

incrementy :: Parser Ibp -> Handle -> IO [Ibp]
incrementy xs h = go (0 :: Int) [] =<< refill h
 where
   go n !acc is = do
     when (n > 0 && n `mod` 10000 == 0) ( putStr "Parsed equations: "
                                 >> print n)
     r <- parseWith (refill h) xs is
     case r of
       Fail _ _ msg -> error msg
       Done bs x
           | B.null bs -> do
              s <- refill h
              if B.null s
                then return $! (x:acc)
                else go (n+1) (x:acc) s
           | otherwise -> go (n+1) (x:acc) bs

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
unwrapBackGauss p rs = let (_, res) =  reify p (\ (_ :: Proxy s) -> first unFp {-symmetricRep-} (rs :: (Fp s Int, [V.Vector Int])))
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
      
-- | Given an ordering and an equality check, partition a list into a
-- triplet of
-- 1. the minimal element w.r.t. the ordering
-- 2. a list of all elements that are equal to 1. with regard to the equality check
-- 3. a list of all other elements.
removeMinAndSplitBy :: (a -> a -> Ordering) -> (a -> a -> Bool) -> [a] -> (a, [a], [a])
removeMinAndSplitBy cmp eq xs = foldl' getMin (head xs, [], []) (tail xs)
  where getMin (!y,!ys, !zs) x = case cmp y x of
          GT -> if eq x y then (x, y:ys, zs) else (x, [], y: (ys Data.List.++ zs))
          _  -> if eq x y then (y, x:ys, zs) else (y, ys, x:zs)

probeStep :: forall s . Reifies s Int
             => ([Row s], [((Int, (Int, Int)), Row s)])
             -- ^ ([finished rows], [( Line number
             --                      , ( original number of terms in equation
             --                      , original index of most complicated integral), equation)])
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
      (comparing (fst . V.head . snd) -- first column with non-zero entry
       `mappend` flip (comparing (snd . snd . fst)) -- originally most com;plicated integral
       `mappend` comparing (fst . snd . fst) -- original number of terms in equation
       `mappend` comparing (fst . fst) -- line number as tie braker
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
      in (ind, addRows (multRow (-x) (snd normalisedPivotRow)) row)
    rows' = filter (not . V.null . snd) (fmap pivotOperation rowsToModify) Data.List.++ ignoreRows
    i' = (fst . fst $ pivotRow) :i
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
testMatrixFwd n xs rs = (rs',d,j,i) where
  (rs', d, j, i) = probeStep ([],  BV.toList . BV.imap (\ k v -> ((k,(V.length v, fst (V.head v))), v)) $ rows m) 1 [] []
  m = evalIbps n xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
            
withMod :: Int -> (forall s . Reifies s Int => ([Row s], Fp s Int, V.Vector Int, V.Vector Int))
           -> ([V.Vector (Int, Int)], Int, V.Vector Int, V.Vector Int)
withMod m x = reify m (\ (_ :: Proxy s) -> (symmetricRep' (x :: ([Row s], Fp s Int, V.Vector Int, V.Vector Int))))
  where symmetricRep' (rs,d,j,i) = (map (V.map (second unFp)) rs,unFp d,j,i)

config :: Config
config = Config { inputFile = def &= args &= typ "FILE"
                , dumpFile = def &= name "d" &= typFile &= help "In addition to the output on stdout, print a list of newline-separated equation numbers to FILE.  Note that the equations are zero-indexed."
                , intName = "Int" &= help "This is used to control the name of the function representing integrals in the input file.  The default is Int."
                , invariants = def &= name "i" &= help "Add the symbol ITEM to the list of variables that appear in the polynomials."
                , sortList = False &= help "Sort the list of linearly independent equations.  Otherwise, prints a permutation that brings the matrix as close to upper triangular form as possible."
                , backsub = False &= help "After forward elimination, perform backward elimination in order to determine which master integrals appear in the result for each integral."
                , rMax = def &= name "r" &= help "Maximal number of dots expected to be reduced."
                , sMax = def &= name "s" &= help "Maximal number of scalar products expected to be reduced."}
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
               incrementy (ibp (B.pack $ intName c) invariants')
  let (outerIntegrals, innerIntegrals) =
        both (map fst . Map.toList . Map.fromList . (`zip` repeat ()))
        (partition (isBeyond c) (concatMap (BV.toList . getIntegrals) equations))
      nOuterIntegrals = length outerIntegrals
      integrals = uncurry (Data.List.++) (outerIntegrals, innerIntegrals)
      integralNumbers = both Map.fromList
                        ( zip outerIntegrals [0 :: Int ..]
                        , zip innerIntegrals [nOuterIntegrals ..])
      ibpRows = map (ibpToRow integralNumbers)  equations
  putStr "Number of equations: "
  print (length equations)
  putStr "Number of integrals: "
  print (length integrals)
  putStrLn (concat ["Number of integrals within r="
                   , show (rMax c), ", s=", show (sMax c)
                   , ": ", show (length innerIntegrals)])
  let pList = [3036998333,3036998347,3036998381,3036998401,3036998429,3036998449,3036998477
              ,3036998537,3036998561,3036998563,3036998567,3036998599,3036998611,3036998717
              ,3036998743,3036998759,3036998761,3036998777,3036998803,3036998837,3036998843
              ,3036998849,3036998857,3036998873,3036998903,3036998933,3036998957,3036998963
              ,3036998977,3036998989,3036998999,3036999001,3036999019,3036999023,3036999061
              ,3036999067,3036999079,3036999089,3036999101,3036999113,3036999137,3036999157
              ,3036999167,3036999209,3036999233,3036999271,3036999283,3036999293,3036999307
              ,3036999319,3036999341,3036999379,3036999403,3036999431,3036999439,3036999443
              ,3036999457,3036999467,3036999473,3036999487,3036999499,3036999727,3036999733
              ,3036999737,3036999739,3036999761,3036999769,3036999773,3036999803,3036999811
              ,3036999817,3036999821,3036999841,3036999877,3036999887,3036999899,3036999941
              ,3036999983,3036999991,3037000013,3037000039,3037000069,3037000103,3037000111
              ,3037000121,3037000159,3037000177,3037000181,3037000193,3037000249,3037000289
              ,3037000303,3037000331,3037000333,3037000391,3037000399,3037000427,3037000429
              ,3037000453,3037000493] :: [Int]
  p <- liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
  xs <- V.generateM (length invs) (\_ -> getRandomR (1,p))
  putStr "Probing for p = "
  print p
  putStr "Random points: "
  print (V.toList xs)
  startReductionTime <- getCurrentTime
  let (!rs',_,!j,!i) = withMod p $ testMatrixFwd (length integrals) xs ibpRows
  putStr "Number of linearly independent equations: "
  print (V.length i)
  let eqList = (if sortList c then sort else id) (V.toList i)
  putStrLn "Indices of linearly independent equations (starting at 0):"
  mapM_ print eqList
  endReductionTime <- getCurrentTime
  when (dumpFile c /= "") (withFile (dumpFile c) WriteMode (\h -> mapM_ (hPrint h) eqList))

  let (reducibleIntegrals, irreducibleIntegrals) =
        partition (\ (k,_) -> let n = fromMaybe (error  "integral not found.") (lookupInPair k integralNumbers)
                          in V.elem n j) (drop nOuterIntegrals $ zip integrals [0 :: Int ..])
  putStrLn "Integrals that can be reduced with these equations:"
  mapM_ (print . fst) reducibleIntegrals
  putStrLn "Possible Master Integrals:"
  mapM_ (print . fst) irreducibleIntegrals

  when (backsub c) $ do
    putStrLn "Performing backward elimination."
    let rs'' = unwrapBackGauss p $
               backGauss ([],  map (V.map (second normalise))
                                   ((reverse
                                     . dropWhile ((<nOuterIntegrals) . fst . V.head)
                                     . reverse) rs'))
    putStrLn "Final representations of the integrals will look like:"
    mapM_ (printRow integralNumbers) rs''
  putStr "The probability that too many equations were discarded is less than "
  print (1 - product [1- (fromIntegral x / fromIntegral p) | x <- [1..V.length i]] :: Double)
  putStrLn "Timings (wall time):"
  putStr "Parsing and preparing equations: "
  print $ diffUTCTime startReductionTime startParseTime
  putStr "Solving Equations: "
  print $ diffUTCTime endReductionTime startReductionTime

    where printRow intmap r = do
            putStr $ showIntegral intmap (V.head r)
            putStr " -> {"
            putStr (intercalate ", " (map (showIntegral intmap) (V.toList $ V.tail r)))
            putStrLn "}"
          showIntegral intmap n =
            let (elt, n') = if n < Map.size (fst intmap)
                            then Map.elemAt n (fst intmap)
                            else Map.elemAt (n-Map.size (fst intmap)) (snd intmap)
            in assert (n==n') $ show elt
  
