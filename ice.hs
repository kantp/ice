{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
module Main
       (main)
       where

import           Codec.BMP (BMP, packRGBA32ToBMP, writeBMP)
import           Control.Arrow
import           Control.Exception (assert)
import           Control.Monad
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map)
import           Data.Array.Repa.Repr.Vector (V)
import           Data.Attoparsec
import           Data.ByteString (pack)
import qualified Data.ByteString.Char8 as B
import           Data.Either (partitionEithers)
import           Data.Function (on)
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import           Data.Time
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Data.Word (Word8)
import           Ice.Fp
import           Ice.ParseIbp
import           Ice.Types
import           System.Console.CmdArgs
import           System.IO

-- | A list of pre-generated prime numbers such that the square just fits into a 64bit Integer.
pList :: [Int]
pList = [3036998333,3036998347,3036998381,3036998401,3036998429,3036998449,3036998477
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
        ,3037000453,3037000493]

-- | Given the supposed rank of the system and the prime number used,
-- calculate an upper bound on the probability of failure.
getBound :: Int -> Int -> Double
getBound r p = 1 - product [1- (fromIntegral x / fromIntegral p) | x <- [1..r]]

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

ibpToRow :: (Map.Map SInt Int, Map.Map SInt Int) -> Ibp -> Equation
ibpToRow table (Ibp x) = BV.fromList (doCombine $ sortBy (comparing fst) row)
  where
    row = map
          (\ line ->
            ( fromMaybe (error "integral not found.") (lookupInPair (ibpIntegral line) table)
            , (ibpCfs line, ibpExps line))) (BV.toList x)
    doCombine [] = []
    doCombine ((i, x): xs) = combine [] (i, ( R.delay *** R.delay) x) xs
    combine :: [(Int, (R.Array V R.DIM1 Integer, R.Array R.U R.DIM2 Word8))] -> (Int, (R.Array R.D R.DIM1 Integer, R.Array R.D R.DIM2 Word8)) -> [(Int, (R.Array V R.DIM1 Integer, R.Array R.U R.DIM2 Word8))] -> [(Int, (R.Array V R.DIM1 Integer, R.Array R.U R.DIM2 Word8))]
    combine acc elt [] = reverse (second (R.computeS *** R.computeS) elt :acc)
    combine acc (i,elt) ((i',elt'):xs)
      | i == i' = combine acc (i,(R.append (fst elt) (R.delay $ fst elt'), R.append (snd elt) (R.delay $ snd elt'))) xs
      | otherwise = combine ( (i, (R.computeS *** R.computeS) elt) :acc) (i',(R.delay *** R.delay) elt') xs

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
      
-- | split equations into linearly independent and linealy dependent
-- ones (given the list i of linearly independent equations),
-- preserving the permutation.
partitionEqs :: [Int] -> [a] -> ([a], [a])
partitionEqs is rs = first reverse . (map snd *** map snd) $ foldl' step ([], rs') is
  where
    rs' = [(i,rs Data.List.!! i) | i <- [0..length rs - 1]]
    step (indep, dep) i = (eq:indep, dep')
      where ([eq], dep') = partition ((==i) . fst) dep

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
       `mappend` flip (comparing (snd . snd . fst)) -- originally most complicated integral
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

performForwardElim :: Handle -> Double -> Int -> Int -> [Equation]
                      -> IO ([V.Vector (Int, Int)], V.Vector Int, V.Vector Int, Int)
performForwardElim h goal nInvs nInts eqs = do
  p <- liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
  xs <- V.generateM nInvs (\_ -> getRandomR (1,p))
  hPutStrLn h ("Probing for p = " Data.List.++ show p)
  hPutStrLn h ("Random points: " Data.List.++ show (V.toList xs))
  let (!rs',_,!j,!i) = withMod p $ testMatrixFwd nInts xs eqs
      r = V.length i
      bound = getBound r p
  showBound bound
  if bound < goal
    then return (rs', j, i, p)
    else let redoTest r bound rs = do
               hPutStrLn h "Iterating to decrease probability of failure."
               p <- liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
               xs <- V.generateM nInvs (\_ -> getRandomR (1,p))
               let result = unwrapForwardSubTest p $
                            startFwdSubTest nInts r xs rs
               case result of
                 Good bound' -> let bound'' = bound * bound'
                                in
                                 showBound bound'' >>
                                 if bound'' < goal then return (rs', j, i, p)
                                 else redoTest r bound'' rs
                 Restart -> hPutStrLn h "Unlucky evaluation point(s), restarting." >>
                   performForwardElim h goal nInvs nInts eqs
                 Unlucky -> hPutStrLn h "Unlucky evaluation point, discarding." >>
                   redoTest r bound splitRows
             splitRows = partitionEqs (V.toList i) eqs
         in redoTest r bound splitRows
  where showBound b = hPutStrLn h ("The probability that too many equations were discarded is less than " Data.List.++ show b)

unwrapForwardSubTest :: Int
                        -> (forall s . Reifies s Int => (Fp s Int, TestResult))
                        -> TestResult
unwrapForwardSubTest m f =
  snd $ reify m (\ (_ :: Proxy s) -> first unFp (f :: (Fp s Int, TestResult)))

startFwdSubTest :: forall s . Reifies s Int
                   => Int -> Int -> V.Vector Int
                   -> ([Equation], [Equation])
                   -> (Fp s Int, TestResult)
startFwdSubTest nInts r xs rs =
  let xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
      evaldRs = both (BV.toList . rows . evalIbps nInts xs') rs
  in forwardSubTest r (snd evaldRs) (fst evaldRs) 1
forwardSubTest :: forall s . Reifies s Int
              => Int -> [Row s] -> [Row s] -> Fp s Int -> (Fp s Int, TestResult)
forwardSubTest r zeroRows rs d
  | null rs = (d', if null zeroRows then Good (getBound r (getModulus d)) else Unlucky)
  -- | null zeroRows = (d', Good)
  | otherwise = if null failedRs && null failedZeroRows
                then forwardSubTest r zeroRows' rs' d'
                else (d, Restart)
  where
    pivotRow : rowsToModify = rs
    (pivotColumn, pivotElement) = V.head pivotRow
    normalisedPivotRow = multRow (recip pivotElement) pivotRow
    d' = d * pivotElement
    pivotOperation row =
      let (k,x) = V.head row
      in case compare k pivotColumn of
        GT -> Left row
        EQ -> Left $ addRows (multRow (-x) normalisedPivotRow) row
        LT -> Right "Non-zero element left of pivot row."
    mapPivotOp rows = first (filter (not . V.null)) (partitionEithers $ fmap pivotOperation rows)
    (rs', failedRs) = mapPivotOp rowsToModify
    (zeroRows', failedZeroRows) = mapPivotOp zeroRows

evalIbps :: forall s . Reifies s Int
            => Int
            -> Array U DIM1 (Fp s Int)
            -> [Equation]
            -> Matrix s
evalIbps n xs rs = Matrix { nCols = n, rows = rs' } where
  rs' = BV.fromList (map treatRow rs)
  treatRow r = V.filter ((/=0) . snd) $ V.convert $ BV.map (second evalPoly) r
  evalPoly (cs, es) = multiEval xs (Poly (R.computeS $ R.map fromInteger cs) es)

testMatrixFwd :: forall s . Reifies s Int
                 => Int
                 -> V.Vector Int
                 -> [Equation]
                 -> ([Row s], Fp s Int, V.Vector Int, V.Vector Int)
testMatrixFwd n xs rs = (rs',d,j,i) where
  (rs', d, j, i) = probeStep ([],  BV.toList . BV.imap (\ k v -> ((k,(V.length v, fst (V.head v))), v)) $ rows m) 1 [] []
  m = evalIbps n xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int))
            
withMod :: Int -> (forall s . Reifies s Int => ([Row s], Fp s Int, V.Vector Int, V.Vector Int))
           -> ([V.Vector (Int, Int)], Int, V.Vector Int, V.Vector Int)
withMod m x = reify m (\ (_ :: Proxy s) -> (symmetricRep' (x :: ([Row s], Fp s Int, V.Vector Int, V.Vector Int))))
  where symmetricRep' (rs,d,j,i) = (map (V.map (second unFp)) rs,unFp d,j,i)

sparsityBMP :: Int -> [V.Vector Int] -> BMP
sparsityBMP width rs = packRGBA32ToBMP width (length rs) rgba
  where
    rgba = pack . concatMap (buildRow . V.toList) $ rs
    black = [0,0,0,255] :: [Word8]
    white = [255,255,255,255] :: [Word8]
    buildRow r = concat $ unfoldr step (0,r)
    step (i,r)
      | i >= width = Nothing
      | null r = Just (white, (i+1, r))
      | head r == i = Just (black, (i+1, tail r))
      | otherwise = Just (white, (i+1, r))

config :: Config
config = Config { inputFile = def &= args &= typ "FILE"
                , dumpFile = def &= name "d" &= typFile &= help "In addition to the output on stdout, print a list of newline-separated equation numbers to FILE.  Note that the equations are zero-indexed."
                , logFile = "ice.log" &= name "l" &= help "Path to the logfile."
                , intName = "Int" &= help "This is used to control the name of the function representing integrals in the input file.  The default is Int."
                , invariants = def &= name "i" &= help "Add the symbol ITEM to the list of variables that appear in the polynomials."
                , sortList = False &= help "Sort the list of linearly independent equations.  Otherwise, prints a permutation that brings the matrix as close to upper triangular form as possible."
                , backsub = False &= help "After forward elimination, perform backward elimination in order to determine which master integrals appear in the result for each integral."
                , rMax = def &= name "r" &= help "Maximal number of dots expected to be reduced."
                , sMax = def &= name "s" &= help "Maximal number of scalar products expected to be reduced."
                , visualize = False &= help "Draw images of the sparsity pattern of original, reduced, and solved matrices."
                , failBound = 1 &= help "Repeat forward elimination to decrease probability of failure below this."
                , pipes = False &= name "p" &= help "use stdin and stdout for communication instead of files."}
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
  lFile <- openFile (logFile c) WriteMode
  let lPutStr = hPutStr lFile
      lPutStrLn = hPutStrLn lFile
  lPutStrLn "ICE -- Integration-By-Parts Chooser of Equations"
  lPutStr "Command line arguments: "
  lPutStrLn $ show c
  let invariants' = zip [0..] (map B.pack invs)
  startParseTime <- getCurrentTime
  equations <-
    if pipes c
       then incrementy (ibp (B.pack $ intName c) invariants') stdin
       else liftM reverse $ withFile eqFile ReadMode $
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
  lPutStr "Number of equations: "
  lPutStrLn $ show (length equations)
  lPutStr "Number of integrals: "
  lPutStrLn $ show (length integrals)
  lPutStrLn (concat ["Number of integrals within r="
                   , show (rMax c), ", s=", show (sMax c)
                   , ": ", show (length innerIntegrals)])
  startReductionTime <- getCurrentTime
  (rs', j, i, p) <- performForwardElim lFile (failBound c) (length invs) (length integrals) ibpRows
  lPutStr "Number of linearly independent equations: "
  lPutStrLn $ show (V.length i)
  let eqList = (if sortList c then sort else id) (V.toList i)
  lPutStrLn "Indices of linearly independent equations (starting at 0):"
  mapM_ print eqList
  mapM_ (lPutStrLn . show) eqList
  endReductionTime <- getCurrentTime
  when (visualize c) (writeBMP (inputFile c Data.List.++ ".bmp") (sparsityBMP (length integrals) (map (\ n -> map (V.convert . BV.map fst) ibpRows !! n) (V.toList . V.reverse $ i))))
  when (visualize c) (writeBMP (inputFile c Data.List.++ ".forward.bmp") (sparsityBMP (length integrals) (map (V.map fst) rs')))
  when (dumpFile c /= "") (withFile (dumpFile c) WriteMode (\h -> mapM_ (hPrint h) eqList))

  let (reducibleIntegrals, irreducibleIntegrals) =
        partition (\ (k,_) -> let n = fromMaybe (error  "integral not found.") (lookupInPair k integralNumbers)
                          in V.elem n j) (drop nOuterIntegrals $ zip integrals [0 :: Int ..])
  lPutStrLn "Integrals that can be reduced with these equations:"
  mapM_ (lPutStrLn . show . fst) reducibleIntegrals
  lPutStrLn "Possible Master Integrals:"
  mapM_ (lPutStrLn . show . fst) irreducibleIntegrals

  when (backsub c) $ do
    lPutStrLn "Performing backward elimination."
    let rs'' = unwrapBackGauss p $
               backGauss ([],  map (V.map (second normalise))
                                   ((reverse
                                     . dropWhile ((<nOuterIntegrals) . fst . V.head)
                                     . reverse) rs'))
    lPutStrLn "Final representations of the integrals will look like:"
    mapM_ (lPutStrLn . printRow integralNumbers)  rs''
    when (visualize c) (writeBMP (inputFile c Data.List.++ ".solved.bmp") (sparsityBMP (length integrals) (reverse rs'')))

  lPutStrLn "Timings (wall time):"
  lPutStr "Parsing and preparing equations: "
  lPutStrLn $ show $ diffUTCTime startReductionTime startParseTime
  lPutStr "Solving Equations: "
  lPutStrLn $ show $ diffUTCTime endReductionTime startReductionTime
  hClose lFile

    where printRow intmap r =
            concat [showIntegral intmap (V.head r)
                   , " -> {"
                   , intercalate ", " (map (showIntegral intmap) (V.toList $ V.tail r))
                   , "}"]
          showIntegral intmap n =
            let (elt, n') = if n < Map.size (fst intmap)
                            then Map.elemAt n (fst intmap)
                            else Map.elemAt (n-Map.size (fst intmap)) (snd intmap)
            in assert (n==n') $ show elt
  
