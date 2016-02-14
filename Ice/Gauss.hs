{-|
Module: Ice.Gauss
Description: Functions for Gaussian elimination used in Ice.
-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Ice.Gauss
       (
       -- * Forward elimination
         performElimination
       -- * Backward elimination
       , performBackElim
       -- * Auxiliary functions
       , choosePoints)
       where

import           Control.Arrow
import           Control.Monad.RWS
import           Control.Monad.Random
import qualified Data.Array.Repa as R
import           Data.Array.Repa hiding (map, (++))
import           Data.Int (Int64)
import           Data.List
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
import qualified Data.Vector as BV
import qualified Data.Vector.Unboxed as V
import           Ice.Fp
import           Ice.Types


-- | Perform forward elimination, either once or many times, depending
-- on the desired upper bound for the probability of failure.
performElimination :: IceMonad ()
performElimination = do
  s <- gets system
  c <- ask
  (p, rs', _, j, i) <-  case s of
        FpSystem p _ rs -> return $ withMod p $ probeStep [] (buildRowTree (eqsToRows rs)) 1 [] []
        PolynomialSystem _ -> iteratedForwardElim
        FpSolved _ _ _ _ -> error "Internal error: tried solving a solved system. Please report this as a bug."
  let i' = (if sortList c then sort else id) (V.toList i)
  modify (\ x -> x {system = FpSolved p rs' i' j})
  where
    -- | Inject modulus to be used in the forward elimination.
    withMod :: Int64
              -> (forall s . Reifies s Int64 => EliminationResult s)
              -> (Int64, [V.Vector (Int, Int64)], Int64, V.Vector Int, V.Vector Int)
    withMod m x = reify m (\ (_ :: Proxy s) -> (unwrap (x :: EliminationResult s)))
      where unwrap (EliminationResult p rs d j i) = (p,map (V.map (second unFp)) rs, unFp d, j, i)
    eqsToRows :: forall s . Reifies s Int64 => [Equation Int64] -> BV.Vector (Row s)
    eqsToRows = BV.fromList . map (V.convert . BV.map (second fromIntegral))


-- | Performs forward elimination on a linear system over F_p.
probeStep :: forall s . Reifies s Int64
             => [Row s]
             -> RowTree s
             -> Fp s Int64
             -> [Int]
             -> [Int]
             -> EliminationResult s
probeStep !rsDone !rs !d !j !i
  | Map.null rs = EliminationResult p rsDone  d (V.fromList . reverse $ j) (V.fromList . reverse $ i)
  | otherwise =
    probeStep rsDone' rows' d' j' i'
  where
    (pivotRow, otherRows) = Map.deleteFindMin rs
    (RowKey _ _ _ pivotRowNumber) = fst pivotRow
    (pivotColumn, pivotElement) = (V.head . snd) pivotRow

    (rowsToModify, ignoreRows) = Map.split (RowKey (pivotColumn+1) 0 0 0) otherRows
    invPivotElement = recip pivotElement
    !normalisedPivotRow = second (multRow invPivotElement) pivotRow
    d' = d * pivotElement
    j' = pivotColumn:j
    pivotOperation !row =
      let (_,x) = V.head row
      in addRows (multRow (-x) (snd normalisedPivotRow)) row
    modifiedRows = updateRowTree pivotOperation rowsToModify
    rows' = foldl' (\ m (k, v) -> Map.insert k v m) ignoreRows modifiedRows
    i' = pivotRowNumber:i
    rsDone' = snd normalisedPivotRow:rsDone
    p = getModulus d

-- | This function solves multiple images of the original system, in
-- order to reduce the bound on the probability of failure below the
-- value specified by the --failbound option.
iteratedForwardElim :: IceMonad (Int64, [V.Vector (Int, Int64)], Int64, V.Vector Int, V.Vector Int)
iteratedForwardElim = do
  PolynomialSystem eqs <- gets system
  goal <- asks failBound
  (p0, xs0) <- choosePoints
  let (!rs',_,!j,!i) = withMod p0 $ oneForwardElim xs0 eqs
      r0 = V.length i
      bound0 = getBound (fromIntegral r0) p0
      showBound b = info $ "The probability that too many equations were discarded is less than " ++ show b ++ "\n"
  showBound bound0
  if bound0 < goal
    then return (p0, rs', undefined, j, i)
    else let redoTest r bound rs = do
               info "Iterating to decrease probability of failure."
               (p, xs) <- choosePoints
               let (_,_,_,i') = withMod p $ oneForwardElim xs eqs
                   r' = V.length i'
                   result = case compare (r,i) (r',i') of
                     EQ -> Good (getBound (fromIntegral r) p)
                     LT -> Restart
                     GT -> Unlucky
               case result of
                 Good bound' -> let bound'' = bound * bound'
                                in
                                 showBound bound'' >>
                                 if bound'' < goal then return (p, rs', undefined, j, i)
                                 else redoTest r bound'' rs
                 Restart -> info "Unlucky evaluation point(s), restarting." >>
                   iteratedForwardElim
                 Unlucky -> info "Unlucky evaluation point, discarding." >>
                   redoTest r bound splitRows
             splitRows = partitionEqs (V.toList i) eqs
         in redoTest r0 bound0 splitRows
  where
    withMod :: Int64
              -> (forall s . Reifies s Int64
                       => ([Row s], Fp s Int64, V.Vector Int, V.Vector Int))
              -> ([V.Vector (Int, Int64)], Int64, V.Vector Int, V.Vector Int)
    withMod m x = reify m (\ (_ :: Proxy s) -> (unwrap (x :: ([Row s], Fp s Int64, V.Vector Int, V.Vector Int))))
    unwrap (rs,d,j,i) = (map (V.map (second unFp)) rs,unFp d,j,i)

-- | Given the supposed rank of the system and the prime number used,
-- calculate an upper bound on the probability of failure.
getBound :: Int64 -> Int64 -> Double
getBound r p = 1 - product [1- (fromIntegral x / fromIntegral p) | x <- [1..r]]

-- | split equations into linearly independent and linealy dependent
-- ones (given the list i of linearly independent equations),
-- preserving the permutation.
partitionEqs :: [Int] -> [a] -> ([a], [a])
partitionEqs is rs = first reverse . (map snd *** map snd) $ foldl' step ([], rs') is
  where
    rs' = [(i,rs Data.List.!! i) | i <- [0..length rs - 1]]
    step (indep, dep) i = (eq:indep, dep')
      where ([eq], dep') = partition ((==i) . fst) dep

-- | Maps a linear system over polynomials to F_p, and performs forward elimination.
oneForwardElim :: forall s . Reifies s Int64
                   => V.Vector Int64
                   -> [Equation MPoly]
                   -> ([Row s], Fp s Int64, V.Vector Int, V.Vector Int)
oneForwardElim xs rs = (rs',d,j,i) where
  (EliminationResult _ rs' d j i) = probeStep [] (buildRowTree m) 1 [] []
  m = evalIbps xs' rs
  xs' = fromUnboxed (Z :. V.length xs) (V.map normalise xs :: V.Vector (Fp s Int64))

-- | Evaluate the polynomials in the IBP equations.
evalIbps :: forall s . Reifies s Int64
            => Array U DIM1 (Fp s Int64)
            -> [Equation MPoly]
            -> BV.Vector (Row s)
evalIbps xs rs = BV.fromList (map treatRow rs)  where
  {-# INLINE toPoly #-}
  toPoly (MPoly (cs, es)) = Poly (R.fromUnboxed (Z :. BV.length cs) $ (V.convert . BV.map fromInteger) cs) es
  treatRow r = V.filter ((/=0) . snd) $ V.zip (V.convert (BV.map fst r)) (multiEvalBulk xs (BV.map (toPoly . snd) r))

performBackElim :: IceMonad ()
performBackElim = do
  info "Perform Backwards elimination.\n"
  forward@(FpSolved p rs _ _) <- gets system
  nOuter <- liftM (Map.size . fst) $ gets integralMaps
  let rs' = withMod p $
                    backGauss ([],  map (V.map (second normalise))
                                    ((reverse
                                      . dropWhile ((< nOuter) . fst . V.head)
                                      . reverse) rs))
  modify (\ x -> x { system = forward {image = rs'} })
  where
    withMod :: Int64
      -> (forall s . Reifies s Int64 => (Fp s Int64, [V.Vector (Int, Fp s Int64)]))
      -> [V.Vector (Int, Int64)]
    withMod p rs =
      let (_, res) = reify p (\ (_ :: Proxy s) -> (unFp *** map (V.map (second unFp))) (rs :: (Fp s Int64, [V.Vector (Int, Fp s Int64)])))
      in res
-- | Inject a concrete value for the prime number used as modulus in backwards elimination.

-- | Backwards Gaussian elimination.
backGauss :: forall s . Reifies s Int64
             => ([Row s], [Row s])
             -> (Fp s Int64, [Row s])
backGauss (!rsDone, []) = (1, rsDone)
backGauss (!rsDone, !pivotRow:(!rs)) = backGauss (pivotRow:rsDone, rs')
  where
    (pivotColumn, invPivot) = second recip (V.head pivotRow)
    rs' = map pivotOperation rs
    pivotOperation row = case V.find ((==pivotColumn) . fst) row of
      Nothing -> row
      Just (_, elt) -> addRows (multRow (-elt*invPivot) pivotRow) row


-- | A list of pre-generated prime numbers such that the square just fits into a 64bit Integer.
pList :: [Int64]
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

-- | Choose a large prime and an evaluation point randomly.
choosePoints :: IceMonad (Int64, V.Vector Int64)
choosePoints = do
  nInvs <- asks (length . invariants)
  p <- liftIO $ liftM2 (!!) (return pList) (getRandomR (0,length pList - 1))
  xs <- liftIO $ V.generateM nInvs (\_ -> getRandomR (1,p))
  info $ "Probing for p = " ++ show p ++ "\n"
  info $ "Random points: " ++ show (V.toList xs) ++ "\n"
  return (p, xs)
