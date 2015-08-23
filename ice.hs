{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
module Main
       (main)
       where

import           Codec.BMP (BMP, packRGBA32ToBMP, writeBMP)
import           Conduit
import           Control.Arrow
import           Control.Monad
import           Control.Monad.RWS
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map, (++))
import           Data.ByteString (pack)
import qualified Data.ByteString.Char8 as B
import           Data.Conduit.Attoparsec (conduitParser)
import qualified Data.IntMap.Strict as IntMap
import           Data.List
import qualified Data.Map.Strict as Map
import           Data.Maybe
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

-- | Determine which integrals appear in a certain equation.
getIntegrals :: Ibp a -> BV.Vector SInt
getIntegrals (Ibp xs) = BV.map (\ (IbpLine x _) -> x) xs

-- | Transform an equation that is stored as tuples (integral,
-- coefficient) into a sparse matrix row containing entries
-- (#(integral), coefficient).
ibpToRow :: (a -> a -> a) -> (Map.Map SInt (), Map.Map SInt ()) -> Ibp a -> Equation a
ibpToRow combine table (Ibp x) =
  let
    offset = Map.size . fst $ table
    col (IbpLine i _) = fromMaybe (error "integral not found.") (lookupInPair offset i table)
    term (IbpLine _ t) = t
    rowmap = BV.foldl'
             (\ m line -> IntMap.insertWith combine (col line) (term line) m)
             IntMap.empty
             x
  in BV.fromList . IntMap.toList $ rowmap

-- | We keep two sets of integrals.  The first one contains integrals
-- on the boundary that we do not hope to solve without additional
-- equations, the second contains the rest.  We number the whole set
-- of integrals, starting with the integrals at the border.  This
-- function gets the number of an integral.
lookupInPair :: Ord k => Int -> k -> (Map.Map k (), Map.Map k ()) -> Maybe Int
lookupInPair offset k (m1, m2) =
  case Map.lookupIndex k m1 of
    Nothing -> liftM (+ offset) (Map.lookupIndex k m2)
    x -> x

-- | Backwards Gaussian elimination.
backGauss :: Modulus
             -> ([V.Vector (Int, Fp)], [Row])
             -> ([V.Vector (Int, Fp)])
backGauss _ (!rsDone, []) = (rsDone)
backGauss m (!rsDone, !pivotRow:(!rs)) = backGauss m (pivotRow:rsDone, rs')
  where
    (pivotColumn, invPivot) = second (modInv m) (V.head pivotRow)
    rs' = map pivotOperation rs
    pivotOperation row = case V.find ((==pivotColumn) . fst) row of
      Nothing -> row
      Just (_, elt) -> addRows m (multRow m (negateMod m $ (*%) m elt invPivot) pivotRow) row
      
-- | split equations into linearly independent and linealy dependent
-- ones (given the list i of linearly independent equations),
-- preserving the permutation.
partitionEqs :: [Int] -> [a] -> ([a], [a])
partitionEqs is rs = first reverse . (map snd *** map snd) $ foldl' step ([], rs') is
  where
    rs' = [(i,rs Data.List.!! i) | i <- [0..length rs - 1]]
    step (indep, dep) i = (eq:indep, dep')
      where ([eq], dep') = partition ((==i) . fst) dep

-- | This is one step in the forward elimination.
probeStep :: Modulus
             -> ([Row], RowTree)
             -> Fp
             -> [Int]
             -> [Int]
             -> (Int, [Row], Fp, V.Vector Int, V.Vector Int)
probeStep m (!rsDone, !rs) !d !j !i
  | Map.null rs = (m, rsDone, d, V.fromList . reverse $ j, V.fromList . reverse $ i)
  | otherwise =
    probeStep m (rsDone', rows') d' j' i'
  where
    (pivotRow, otherRows) = Map.deleteFindMin rs
    (_,_,_,pivotRowNumber) = fst pivotRow
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow
    (rowsToModify, ignoreRows) = Map.split (pivotColumn+1, 0, 0, 0) otherRows
    invPivotElement = modInv m pivotElement
    normalisedPivotRow = second (multRow m invPivotElement) pivotRow
    d' = (*%) m d pivotElement
    j' = pivotColumn:j
    pivotOperation row =
      let (_,x) = V.head row
      in addRows m (multRow m (negateMod m x) (snd normalisedPivotRow)) row
    modifiedRows = updateRowTree pivotOperation rowsToModify
    rows' = modifiedRows `Map.union` ignoreRows
    i' = pivotRowNumber:i
    rsDone' = snd normalisedPivotRow:rsDone

-- | This function solves multiple images of the original system, in
-- order to reduce the bound on the probability of failure below the
-- value specified by the --failbound option.
iteratedForwardElim :: IceMonad (Int, [V.Vector (Int, Int)], Int, V.Vector Int, V.Vector Int)
iteratedForwardElim = do
  PolynomialSystem eqs <- gets system
  goal <- asks failBound
  (p0, xs0) <- choosePoints
  let (!rs',_,!j,!i) = testMatrixFwd p0 xs0 eqs
      r0 = V.length i
      bound0 = getBound r0 p0
      showBound = tell' "The probability that too many equations were discarded is less than "
  showBound bound0
  if bound0 < goal
    then return (p0, rs', undefined, j, i)
    else let redoTest r bound rs = do
               tell "Iterating to decrease probability of failure."
               (p, xs) <- choosePoints
               let (_,_,_,i') = testMatrixFwd p xs eqs
                   r' = V.length i'
                   result = case compare (r,i) (r',i') of
                     EQ -> Good (getBound r p)
                     LT -> Restart
                     GT -> Unlucky
               case result of
                 Good bound' -> let bound'' = bound * bound'
                                in
                                 showBound bound'' >>
                                 if bound'' < goal then return (p, rs', undefined, j, i)
                                 else redoTest r bound'' rs
                 Restart -> tell "Unlucky evaluation point(s), restarting." >>
                   iteratedForwardElim
                 Unlucky -> tell "Unlucky evaluation point, discarding." >>
                   redoTest r bound splitRows
             splitRows = partitionEqs (V.toList i) eqs
         in redoTest r0 bound0 splitRows

-- | Choose a large prime and an evaluation point randomly.
choosePoints :: IceMonad (Int, V.Vector Int)
choosePoints = do
  nInvs <- asks (length . invariants)
  p <- liftIO $ liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
  xs <- liftIO $ V.generateM nInvs (\_ -> getRandomR (1,p))
  tell' "Probing for p = " p
  tell' "Random points: " (V.toList xs)
  return (p, xs)

-- | Evaluate the polynomials in the IBP equations.
evalIbps :: Modulus
            -> Array U DIM1 Fp
            -> [Equation MPoly]
            -> BV.Vector Row
evalIbps m xs rs = BV.fromList (map treatRow rs)  where
  {-# INLINE toPoly #-}
  toPoly (MPoly (cs, es)) = Poly (R.fromUnboxed (Z :. BV.length cs) $ (V.convert . BV.map fromInteger) cs) es
  treatRow r = V.filter ((/=0) . snd) $ V.zip (V.convert (BV.map fst r)) (multiEvalBulk m xs (BV.map (toPoly . snd) r)) 

-- | During forward elimination, we keep the equations in a sorted
-- tree.  This has the advantage that it is easy to find the next
-- pivot row, find all rows that will be modified in the next step,
-- and reinsert the modified equations.
--   
-- Equations are ordered with the following priority:
--
-- - column index of first non-zero entry
-- - number of times this equations has been modified
-- - number of terms originally in the equation
-- - original row number
type RowTree = Map.Map (Int, Int, Int, Int) Row 
buildRowTree :: BV.Vector Row -> RowTree
buildRowTree = Map.fromList . BV.toList
               . BV.filter (not . V.null . snd)
               . BV.imap (\ i r -> ((fst (V.head r), 0, V.length r, i), r))
updateRowTree :: (Row -> Row) -> RowTree -> RowTree
updateRowTree f rs =
  Map.fromList . Map.elems . Map.filter (not . V.null . snd)  $
  Map.mapWithKey (\ (_, n, t, i) r -> let r' = f r in ((fst (V.head r'), n+1, t, i), r')) rs

-- | Perform a forward elimination.
testMatrixFwd :: Modulus
                 -> V.Vector Int
                 -> [Equation MPoly]
                 -> ([Row], Fp, V.Vector Int, V.Vector Int)
testMatrixFwd p xs rs = (rs',d,j,i) where
  (_, rs', d, j, i) = probeStep p ([], buildRowTree m) 1 [] []
  m = evalIbps p xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map (normalise p) xs :: V.Vector Fp)
            
-- | Produce a bitmap that visualises how sparse a matrix is.
writeSparsityBMP :: Bool -> FilePath -> IceMonad ()
writeSparsityBMP reverseList fName = do
  pattern <- gets (sparsityPattern . system)
  (m1, m2) <- gets integralMaps
  let n = Map.size m1 + Map.size m2
  liftIO (writeBMP fName (sparsityBMP n ((if reverseList then id else reverse) pattern)))

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
    invNames = map B.pack (invariants c)
    integrals eqs = 
        Map.partitionWithKey (\ k _ -> isBeyond c k)
        (Map.fromList $ concatMap (BV.toList . getIntegrals) eqs `zip` repeat ())
    eqSource = if pipes c
               then sourceHandle stdin
               else sourceFile (inputFile c) :: Producer (ResourceT IO) B.ByteString
  if failBound c > 0
    then do
         let invs = zip [0..] invNames
             processEqs table = map (ibpToRow (+) table)
         equations <- liftIO . runResourceT $
                     eqSource
                     =$= conduitParser (ibp (B.pack $ intName c) invs)
                     =$= mapC snd
                     $$ sinkList
         let table = integrals equations
         put (StateData (PolynomialSystem $ processEqs table equations)
                 table
                (Map.size (fst table) + Map.size (snd table)))
    else do
         (p, xs) <- choosePoints
         let invs = zip (V.toList (V.map fromIntegral xs)) invNames
         equations <-liftIO . runResourceT $
                     eqSource
                     =$= conduitParser (evaldIbp (B.pack $ intName c) p invs)
                     =$= mapC snd
                     $$ sinkList
         let table = integrals equations
             processEqs = map (ibpToRow ((+%) p) table)
         put (StateData (FpSystem p xs (processEqs equations))
                 table
                (Map.size (fst table) + Map.size (snd table)))
  s <- get
  endTime <- liftIO getCurrentTime
  nInner <- liftM (Map.size . snd) $ gets integralMaps
  tell' "Number of equations: " (nEq . system $ s)
  tell' "Number of integrals: " (nIntegrals s)
  tell (concat ["Number of integrals within r="
               , show (rMax c), ", s=", show (sMax c)
               , ": ", show nInner])
  tell' "Wall time needed for reading and preparing equations: " (diffUTCTime endTime startTime)
  when (visualize c) (writeSparsityBMP False (inputFile c ++ ".bmp"))

tell' :: (Show a, MonadWriter String m) => String -> a -> m ()
tell' x y = tell (x ++ show y ++ "\n")

performElimination :: IceMonad ()
performElimination = do
  startTime <- liftIO getCurrentTime
  s <- gets system
  c <- ask
  (p, rs', _, j, i) <-  case s of
        FpSystem p _ rs -> return $ probeStep p ([], buildRowTree (eqsToRows p rs)) 1 [] []
        PolynomialSystem _ -> iteratedForwardElim
        FpSolved _ _ _ _ -> error "trying performElimination on solved system."
  let i' = (if sortList c then sort else id) (V.toList i)
  when (visualize c) (
    modify (\ x -> x {system = selectRows i' s}) >>
    writeSparsityBMP False (inputFile c ++ ".select.bmp"))
  modify (\ x -> x {system = FpSolved p rs' i' j})
  nlieq <- gets (length . rowNumbers . system) -- number of linearly independent equations.
  tell' "Number of linearly independent equations: " nlieq
  tell' "Linearly independent equations: " i'
  when (pipes c) (liftIO $ mapM_ print i')
  when (dumpFile c /= "") (liftIO $ withFile (dumpFile c) WriteMode (\ h -> mapM_ (hPrint h) i'))
  -- list possible master integrals
  imaps <- gets integralMaps
  let nOuterIntegrals = Map.size . fst $ imaps
      innerIntegralMap = snd imaps
  let (reducibleIntegrals, irreducibleIntegrals) =
        Map.partitionWithKey (\ k _ -> let n = fromMaybe (error  "integral not found.") (lookupInPair nOuterIntegrals k imaps)
                                     in V.elem n j) innerIntegralMap
  tell' "Integrals that can be reduced with these equations:"
    (map fst (Map.toList reducibleIntegrals))
  tell' "Possible Master Integrals:"
    (map fst (Map.toList irreducibleIntegrals))
  endTime <- liftIO getCurrentTime
  tell' "Wall time needed for reduction: " (diffUTCTime endTime startTime)
  when (visualize c) (writeSparsityBMP True (inputFile c ++ ".forward.bmp"))
                          
eqsToRows :: Modulus -> [Equation Int] -> BV.Vector Row
eqsToRows m = BV.fromList . map (V.convert . BV.map (second (normalise m)))

performBackElim :: IceMonad ()
performBackElim = do
  tell "Perform Backwards elimination.\n"
  forward@(FpSolved p rs _ _) <- gets system
  nOuter <- liftM (Map.size . fst) $ gets integralMaps
  let rs' = backGauss p ([],  map (V.map (second (normalise p)))
                             ((reverse
                               . dropWhile ((< nOuter) . fst . V.head)
                               . reverse) rs))
  modify (\ x -> x { system = forward {image = rs'} })
  s <- get
  c <- ask
  when (visualize c) (writeSparsityBMP False (inputFile c ++ ".solved.bmp"))
  tell "Final representations of the integrals will look like:\n"
  mapM_ (tell . printRow (integralMaps s)) rs'
  where printRow intmap r =
          concat [showIntegral intmap (fst . V.head $ r)
                 , " -> {"
                 , intercalate ", " (map (showIntegral intmap . fst ) (V.toList $ V.tail r))
                 , "}\n"]
        showIntegral intmap n =
          let elt = fst $ if n < Map.size (fst intmap)
                          then Map.elemAt n (fst intmap)
                          else Map.elemAt (n - Map.size (fst intmap)) (snd intmap)
          in show elt

ice :: IceMonad ()
ice = do
  c <- ask
  initialiseEquations
  performElimination
  when (backsub c) performBackElim

main :: IO ()
main = do
  c <- cmdArgs config
  (_, _, messages) <- runRWST ice c undefined
  lFile <- openFile (logFile c) WriteMode
  hPutStrLn lFile messages
  hClose lFile
