{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
module Main
       (main)
       where

import           Codec.BMP (BMP, packRGBA32ToBMP, writeBMP)
import           Conduit
import           Control.Monad
import           Control.Monad.RWS
import           Data.ByteString (pack)
import qualified Data.ByteString.Char8 as B
import           Data.Conduit.Attoparsec (conduitParser)
import           Data.Int (Int64)
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
import           Ice.Gauss
import           Ice.ParseIbp
import           Ice.Types
import           System.Console.CmdArgs
import           System.Environment (getArgs, withArgs)
import           System.IO
import           System.Remote.Monitoring

-- | Determine which integrals appear in a certain equation.
getIntegrals :: Ibp a -> BV.Vector SInt
getIntegrals (Ibp xs) = BV.map (\ (IbpLine x _) -> x) xs

-- | Transform an equation that is stored as tuples (integral,
-- coefficient) into a sparse matrix row containing entries
-- (#(integral), coefficient).
ibpToRow :: Num a => (Map.Map SInt (), Map.Map SInt ()) -> Ibp a -> Equation a
ibpToRow table (Ibp x) =
  let
    offset = Map.size . fst $ table
    col (IbpLine i _) = fromMaybe (error "integral not found.") (integralNumber offset i table)
    term (IbpLine _ t) = t
    rowmap = BV.foldl'
             (\ m line -> IntMap.insertWith (+) (col line) (term line) m)
             IntMap.empty
             x
  in BV.fromList . IntMap.toList $ rowmap

-- | We keep two sets of integrals.  The first one contains integrals
-- on the boundary that we do not hope to solve without additional
-- equations, the second contains the rest.  We number the whole set
-- of integrals, starting with the integrals at the border.  This
-- function gets the number of an integral.
integralNumber :: Ord k => Int -> k -> (Map.Map k (), Map.Map k ()) -> Maybe Int
integralNumber offset k (m1, m2) =
  case Map.lookupIndex k m1 of
    Nothing -> liftM (+ offset) (Map.lookupIndex k m2)
    x -> x

-- | Write a bitmap of the sparsity pattern of the linear system.
writeSparsityBMP :: Bool -> FilePath -> IceMonad ()
writeSparsityBMP reverseList fName = do
  pattern <- gets (sparsityPattern . system)
  (m1, m2) <- gets integralMaps
  let n = Map.size m1 + Map.size m2
  liftIO (writeBMP fName (sparsityBMP n ((if reverseList then id else reverse) pattern)))
  where

-- | Produce a bitmap to illustrate the sparsity pattern of a matrix.
-- This is only for illustrative purposes for small matrices (I used
-- it for a talk once).
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
  info' "Configuration: " c
  let
    invNames = map B.pack (invariants c)
    integrals eqs =
        Map.partitionWithKey (\ k _ -> isBeyond c k)
        (Map.fromList $ concatMap (BV.toList . getIntegrals) eqs `zip` repeat ())
    processEqs table = map (ibpToRow table)
    input = if pipes c
               then sourceHandle stdin
               else sourceFile (inputFile c) :: Producer (ResourceT IO) B.ByteString
    unwrap :: Int64 -> (forall s . Reifies s Int64 => IO [Ibp (Fp s Int64)]) -> IO [Ibp Int64]
    unwrap p x = reify p (\ (_ :: Proxy s) -> liftM ((map . fmap) unFp) (x :: IO [Ibp (Fp s Int64)]) )
  if failBound c > 0
    then do
         let invs = zip [0..] invNames
         equations <- liftIO . runResourceT $
                   input
                   =$= conduitParser (ibp (B.pack $ intName c) invs)
                   =$= mapC snd
                   $$ sinkList
         let table = integrals equations
         put (StateData (PolynomialSystem $ processEqs table equations)
                 table
                (Map.size (fst table) + Map.size (snd table)))
    else do
         let parseAndEval :: Reifies s Int64 => V.Vector Int64 -> IO [Ibp (Fp s Int64)]
             parseAndEval xs = runResourceT $
               input
               =$= conduitParser (evaldIbp (B.pack $ intName c) (zip (V.toList (V.map fromIntegral xs)) invNames))
               =$= mapC snd
               $$ sinkList
         (p, xs) <- choosePoints
         equations <- liftIO $ unwrap p $ parseAndEval xs
         let table = integrals equations
         put (StateData (FpSystem p xs (processEqs table equations))
                 table
                (Map.size (fst table) + Map.size (snd table)))
  s <- get
  endTime <- liftIO getCurrentTime
  nInner <- liftM (Map.size . snd) $ gets integralMaps
  info' "Number of equations: " (nEq . system $ s)
  info' "Number of integrals: " (nIntegrals s)
  info (concat ["Number of integrals within r="
               , show (rMax c), ", s=", show (sMax c)
               , ": ", show nInner])
  info' "Wall time needed for reading and preparing equations: " (diffUTCTime endTime startTime)
  when (visualize c) (writeSparsityBMP False (inputFile c ++ ".bmp"))


printForwardResults :: IceMonad ()
printForwardResults = do
  independentEqs <- gets (rowNumbers . system)
  c <- ask
  -- list indices of linearly independent equations
  info' "Number of linearly independent equations: " (length independentEqs)
  info' "Linearly independent equations: " independentEqs
  when (pipes c) (liftIO $ mapM_ print independentEqs)
  when (dumpFile c /= "") $
    liftIO $ withFile (dumpFile c) WriteMode (\ h -> mapM_ (hPrint h) independentEqs)
  -- list possible master integrals
  imaps <- gets integralMaps
  j <- gets (pivotColumnNumbers . system)
  let nOuterIntegrals = Map.size . fst $ imaps
      innerIntegralMap = snd imaps
      (reducibleIntegrals, irreducibleIntegrals) =
        Map.partitionWithKey
          (\ k _ -> let n = fromMaybe
                             (error  "integral not found.")
                             (integralNumber nOuterIntegrals k imaps)
                   in V.elem n j)
          innerIntegralMap
  info' "Integrals that can be reduced with these equations:"
    (map fst (Map.toList reducibleIntegrals))
  info' "Possible Master Integrals:"
    (map fst (Map.toList irreducibleIntegrals))
  when (visualize c) $ -- print pattern after forward elimination
    writeSparsityBMP True (inputFile c ++ ".forward.bmp")

printBackResults :: IceMonad ()
printBackResults = do
  s <- get
  c <- ask
  rs <- gets (image . system)
  when (visualize c) (writeSparsityBMP False (inputFile c ++ ".solved.bmp"))
  info "Final representations of the integrals will look like:\n"
  mapM_ (info . printRow (integralMaps s)) rs
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
  when (visualize c) $ -- print sparsity pattern before elimination
    writeSparsityBMP False (inputFile c ++ ".bmp")
  startTime <- liftIO getCurrentTime
  performElimination -- get system to upper echelon form, discarding
                     -- lineraly dependent equations
  endTime <- liftIO getCurrentTime
  info' "Wall time needed for reduction: " (diffUTCTime endTime startTime)
  printForwardResults
  when (backsub c) $
    performBackElim >> printBackResults

main :: IO ()
main = do
  xs <- getArgs
  c <- (if null xs then withArgs ["--help"] else id) (cmdArgs config)
  initLog c
  mapM_ (forkServer "localhost") (ekgPort c)
  void $ runRWST ice c undefined
