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
import           Control.Monad
import           Control.Monad.Random
import           Control.Monad.RWS
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map, (++))
import           Data.Attoparsec
import           Data.ByteString (pack)
import qualified Data.ByteString.Char8 as B
import qualified Data.IntMap.Strict as IntMap
import           Data.List
import qualified Data.Map.Strict as Map
import           Data.Maybe
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

readEquations :: Parser (Ibp a) -> Handle -> IO [Ibp a]
readEquations parser h = go (0 :: Int) [] =<< refill h
  where
    go !n !acc !is = do
      when (n > 0 && n `mod` 10000 == 0) ( hPutStr stderr "Parsed equations: "
                                           >> (hPutStr stderr . show) n)
      r <- parseWith (refill h) parser is
      case r of
        Fail _ _ msg -> error msg
        Done bs x
          | B.null bs -> do
            s <- refill h
            if B.null s
              then return $! (x:acc)
              else go (n+1) (x:acc) s
          | otherwise -> go (n+1) (x:acc) bs

getIntegrals :: Ibp a -> BV.Vector SInt
getIntegrals (Ibp xs) = BV.map (\ (IbpLine x _) -> x) xs

ibpToRow :: Num a => (Map.Map SInt (), Map.Map SInt ()) -> Ibp a -> Equation a
ibpToRow table (Ibp x) =
  let
    offset = Map.size . fst $ table
    col (IbpLine i _) = fromMaybe (error "integral not found.") (lookupInPair offset i table)
    term (IbpLine _ t) = t
    rowmap = BV.foldl'
             (\ m line -> IntMap.insertWith (+) (col line) (term line) m)
             IntMap.empty
             x
  in BV.fromList . IntMap.toList $ rowmap

lookupInPair :: Ord k => Int -> k -> (Map.Map k (), Map.Map k ()) -> Maybe Int
lookupInPair offset k (m1, m2) =
  case Map.lookupIndex k m1 of
    Nothing -> liftM (+ offset) (Map.lookupIndex k m2)
    x -> x

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

probeStep :: forall s . Reifies s Int
             => ([Row s], RowTree s)
             -> Fp s Int
             -> [Int]
             -> [Int]
             -> ([Row s], Fp s Int, V.Vector Int, V.Vector Int)
probeStep (!rsDone, !rs) !d !j !i
  | Map.null rs = (rsDone, d, V.fromList . reverse $ j, V.fromList . reverse $ i)
  | otherwise =
    probeStep (rsDone', rows') d' j' i'
  where
    (pivotRow, otherRows) = Map.deleteFindMin rs
    (_,_,_,pivotRowNumber) = fst pivotRow
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow
    (rowsToModify, ignoreRows) = Map.split (pivotColumn+1, 0, 0, 0) otherRows
    invPivotElement = recip pivotElement
    normalisedPivotRow = second (multRow invPivotElement) pivotRow
    d' = d * pivotElement
    j' = pivotColumn:j
    pivotOperation row =
      let (_,x) = V.head row
      in addRows (multRow (-x) (snd normalisedPivotRow)) row
    modifiedRows = updateRowTree pivotOperation rowsToModify
    rows' = modifiedRows `Map.union` ignoreRows
    i' = pivotRowNumber:i
    rsDone' = snd normalisedPivotRow:rsDone

iteratedForwardElim :: IceMonad ([V.Vector (Int, Int)], Int, V.Vector Int, V.Vector Int)
iteratedForwardElim = do
  PolynomialSystem eqs <- gets system
  goal <- asks failBound
  nInvs <- asks (length . invariants)
  p <- liftIO $ liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
  xs <- liftIO $ V.generateM nInvs (\_ -> getRandomR (1,p))
  tell' "Probing for p = " p
  tell' "Random points: " (V.toList xs)
  let (!rs',_,!j,!i) = withMod p $ testMatrixFwd xs eqs
      r = V.length i
      bound = getBound r p
      showBound = tell' "The probability that too many equations were discarded is less than "
  showBound bound
  if bound < goal
    then return (rs', undefined, j, i)
    else let redoTest r bound rs = do
               tell "Iterating to decrease probability of failure."
               p <- liftIO $ liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
               xs <- liftIO $ V.generateM nInvs (\_ -> getRandomR (1,p))
               tell' "Probing for p = " p
               tell' "Random points: " (V.toList xs)
               let (_,_,_,i') = withMod p $ testMatrixFwd xs eqs
                   r' = V.length i'
                   result = case compare (r,i) (r',i') of
                     EQ -> Good (getBound r p)
                     LT -> Restart
                     GT -> Unlucky
               case result of
                 Good bound' -> let bound'' = bound * bound'
                                in
                                 showBound bound'' >>
                                 if bound'' < goal then return (rs', undefined, j, i)
                                 else redoTest r bound'' rs
                 Restart -> tell "Unlucky evaluation point(s), restarting." >>
                   iteratedForwardElim
                 Unlucky -> tell "Unlucky evaluation point, discarding." >>
                   redoTest r bound splitRows
             splitRows = partitionEqs (V.toList i) eqs
         in redoTest r bound splitRows

evalIbps :: forall s . Reifies s Int
            => Array U DIM1 (Fp s Int)
            -> [Equation MPoly]
            -> BV.Vector (Row s)
evalIbps xs rs = BV.fromList (map treatRow rs)  where
  {-# INLINE toPoly #-}
  toPoly (cs, es) = Poly (R.fromUnboxed (Z :. BV.length cs) $ (V.convert . BV.map fromInteger) cs) es
  treatRow r = V.filter ((/=0) . snd) $ V.zip (V.convert (BV.map fst r)) (multiEvalBulk xs (BV.map (toPoly . snd) r)) 

-- | Equations are ordered with the following priority:
--
-- - column index of first non-zero entry
-- - number of times this equations has been modified
-- - number of terms originally in the equation
-- - original row number
type RowTree s = Map.Map (Int, Int, Int, Int) (Row s)
buildRowTree :: BV.Vector (Row s) -> RowTree s
buildRowTree = Map.fromList . BV.toList
               . BV.filter (not . V.null . snd)
               . BV.imap (\ i r -> ((fst (V.head r), 0, V.length r, i), r))
updateRowTree :: (Row s -> Row s) -> RowTree s -> RowTree s
updateRowTree f rs =
  Map.fromList . Map.elems . Map.filter (not . V.null . snd)  $
  Map.mapWithKey (\ (_, n, t, i) r -> let r' = f r in ((fst (V.head r'), n+1, t, i), r')) rs
-- toRowTree :: [(Int, Int, Row s)] -> RowTree s
-- toRowTree rs = Map.fromList (map (\ (x, y, z) -> ((V.length z, x, y), z) ) rs)

testMatrixFwd :: forall s . Reifies s Int
                 => V.Vector Int
                 -> [Equation MPoly]
                 -> ([Row s], Fp s Int, V.Vector Int, V.Vector Int)
testMatrixFwd xs rs = (rs',d,j,i) where
  -- (rs', d, j, i) = probeStep ([],  BV.toList . BV.imap (\ k v -> ((k,(V.length v, fst (V.head v))), v)) $ rows m) 1 [] []
  (rs', d, j, i) = probeStep ([],  buildRowTree m) 1 [] []
  m = evalIbps xs' rs
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

-- | Read a system of equations.
--
-- Depending on the configuration, the system is read from stdin or
-- the value of the parameter inputFile.
--
-- unless the value of failBound is positive, we evaluate the
-- polynomials already during parsing, thus reducing the memory
-- footprint.
initialiseEquations :: IceMonad ()
initialiseEquations = do
  startTime <- liftIO getCurrentTime
  c <- ask
  tell' "Configuration: " c
  let
    parseAction =
        if pipes c then flip ($) stdin -- \ parser -> parser stdin
        else withFile (inputFile c) ReadMode
    invNames = map B.pack (invariants c)
    integrals eqs = 
        Map.partitionWithKey (\ k _ -> isBeyond c k)
        (Map.fromList $ concatMap (BV.toList . getIntegrals) eqs `zip` repeat ())
    processEqs table = map (ibpToRow table)
    parseAndEval :: Reifies s Int => V.Vector Int -> IO [Ibp (Fp s Int)]
    parseAndEval xs = do
      let invs = zip (V.toList (V.map fromIntegral xs)) invNames
          parser = readEquations (evaldIbp (B.pack $ intName c) invs)
      parseAction parser
    unwrap :: Int -> (forall s . Reifies s Int => IO [Ibp (Fp s Int)]) -> IO [Ibp Int]
    unwrap p x = reify p (\ (_ :: Proxy s) -> liftM ((map . fmap) unFp) (x :: IO [Ibp (Fp s Int)]) )
  if failBound c > 0
    then do
         let invs = zip [0..] invNames
             parser = readEquations (ibp (B.pack $ intName c) invs)
         equations <- liftIO $ parseAction parser
         let table = integrals equations
         put (StateData (PolynomialSystem $ processEqs table equations)
                 table
                (Map.size (fst table) + Map.size (snd table)))
    else do
         p <- liftIO $ liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
         xs <- liftIO $ V.generateM (length $ invariants c) (\_ -> getRandomR (1,p))
         equations <- liftIO $ unwrap p $ parseAndEval xs
         let table = integrals equations
         put (StateData (FpSystem p xs (processEqs table equations))
                 table
                (Map.size (fst table) + Map.size (snd table)))
  s <- get
  endTime <- liftIO getCurrentTime
  tell' "Number of equations: " (nEq . system $ s)
  tell' "Number of integrals: " (nIntegrals s)
  tell' "Wall time needed for reading and preparing equations: " (diffUTCTime endTime startTime)

tell' :: (Show a, MonadWriter String m) => String -> a -> m ()
tell' x y = tell (x ++ show y ++ "\n")

performElimination :: IceMonad ()
performElimination = do
  startTime <- liftIO getCurrentTime
  s <- gets system
  (rs', _, j, i) <-  case s of
        FpSystem p as rs -> return $ withMod p $ probeStep ([], buildRowTree (eqsToRows rs)) 1 [] []
        PolynomialSystem _ -> iteratedForwardElim
  modify (\x -> x {system = FpSolved rs' i j})
  endTime <- liftIO getCurrentTime
  nlieq <- gets (V.length . rowNumbers . system) -- number of linearly independent equations.
  tell' "Number of linearly independent equations: " nlieq
  tell' "Wall time needed for reduction: " (diffUTCTime endTime startTime)
                          
eqsToRows :: forall s . Reifies s Int => [Equation Int] -> BV.Vector (Row s)
eqsToRows xs = BV.fromList $ map (V.convert . BV.map (second fromIntegral)) xs

reportResult :: IceMonad ()
reportResult = do
  s <- gets system
  case s of
    FpSolved image rowNumbers pivotColumnNumbers ->
      tell' "Linearly independent equations: " rowNumbers

main :: IO ()
main = do
  c <- cmdArgs config
  (result, finalState, log) <- runRWST ice c undefined
  putStrLn log
  print finalState
  where
    ice = do
      initialiseEquations
      performElimination
      reportResult
  

-- ice :: IO (IceState ())
-- ice = do
{-
  lPutStrLn (concat ["Number of integrals within r="
                    , show (rMax c), ", s=", show (sMax c)
                    , ": ", show (Map.size innerIntegralMap)])
  startReductionTime <- getCurrentTime
  (rs', j, i, p) <- iteratedForwardElim lFile (failBound c) (length invs) nIntegrals ibpRows
  lPutStr "Number of linearly independent equations: "
  lPutStrLn $ show (V.length i)
  let eqList = (if sortList c then sort else id) (V.toList i)
  lPutStrLn "Indices of linearly independent equations (starting at 0):"
  mapM_ print eqList
  mapM_ (lPutStrLn . show) eqList
  endReductionTime <- getCurrentTime
  when (visualize c) (writeBMP (inputFile c ++ ".bmp") (sparsityBMP nIntegrals
        (map (\ n -> map (V.convert . BV.map fst) ibpRows !! n) [0..length ibpRows - 1])))
  when (visualize c) (writeBMP (inputFile c ++ ".select.bmp") (sparsityBMP nIntegrals (map (\ n -> map (V.convert . BV.map fst) ibpRows !! n) (V.toList . V.reverse $ i))))
  when (visualize c) (writeBMP (inputFile c ++ ".forward.bmp") (sparsityBMP nIntegrals (map (V.map fst) rs')))
  when (dumpFile c /= "") (withFile (dumpFile c) WriteMode (\h -> mapM_ (hPrint h) eqList))

  let (reducibleIntegrals, irreducibleIntegrals) =
        Map.partitionWithKey (\ k _ -> let n = fromMaybe (error  "integral not found.") (lookupInPair nOuterIntegrals k (outerIntegralMap, innerIntegralMap))
                                     in V.elem n j) innerIntegralMap
  lPutStrLn "Integrals that can be reduced with these equations:"
  mapM_ (lPutStrLn . show . fst) (Map.toList reducibleIntegrals)
  lPutStrLn "Possible Master Integrals:"
  mapM_ (lPutStrLn . show . fst) (Map.toList irreducibleIntegrals)

  when (backsub c) $ do
    lPutStrLn "Performing backward elimination."
    let rs'' = unwrapBackGauss p $
               backGauss ([],  map (V.map (second normalise))
                                   ((reverse
                                     . dropWhile ((<nOuterIntegrals) . fst . V.head)
                                     . reverse) rs'))
    lPutStrLn "Final representations of the integrals will look like:"
    mapM_ (lPutStrLn . printRow (outerIntegralMap, innerIntegralMap))  rs''
    when (visualize c) (writeBMP (inputFile c ++ ".solved.bmp") (sparsityBMP nIntegrals (reverse rs'')))

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
            let elt = fst $ if n < Map.size (fst intmap)
                                      then Map.elemAt n (fst intmap)
                                      else Map.elemAt (n - Map.size (fst intmap)) (snd intmap)
            in show elt
-}
