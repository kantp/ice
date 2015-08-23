{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeSynonymInstances      #-}
module Ice.Types

where

import           Control.Monad.RWS
import qualified Data.Array.Repa        as R
import           Data.List              (intercalate)
import qualified Data.Map.Strict        as Map
import           Data.Ord
import qualified Data.Vector            as BV
import qualified Data.Vector.Unboxed    as V
import           Data.Word              (Word8)
import           System.Console.CmdArgs


-- | Configuration via cmdargs library.
data Config = Config { inputFile  :: FilePath
                     , dumpFile   :: FilePath
                     , logFile    :: FilePath
                     , intName    :: String
                     , invariants :: [String]
                     , sortList   :: Bool
                     , backsub    :: Bool
                     , rMax       :: Int
                     , sMax       :: Int
                     , visualize  :: Bool
                     , failBound  :: Double
                     , pipes      :: Bool
                     } deriving (Show, Data, Typeable)

-- | Default values of configuration.
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


-- | State of the computation: the linear system, the sorted
-- integrals, and number of integrals.
data StateData = StateData { system       :: LinSystem
                           , integralMaps :: (Map.Map SInt (), Map.Map SInt ())
                           , nIntegrals   :: Int
                           } deriving Show

-- | State Monad of Ice.
type IceMonad a = RWST Config String StateData IO a

-- | A linear system can either be a system with polynomial entries,
-- an image under evaluation modulo a prime, or a solution of an
-- image.
data LinSystem = PolynomialSystem [Equation MPoly]
               | FpSystem { prime :: Int
                          , as    :: V.Vector Int
                          , mijs  :: [Equation Int] }
               | FpSolved { prime              :: Int
                          , image              :: [V.Vector (Int, Int)]
                          , rowNumbers         :: [Int]
                          , pivotColumnNumbers :: V.Vector Int} deriving Show

-- | Count the number of equations in a linear system.
nEq :: LinSystem -> Int
nEq (PolynomialSystem xs) = length xs
nEq (FpSystem _ _ xs) = length xs
nEq (FpSolved _ _ _ xs) = V.length xs

-- | Select a subset of rows from a system of equations.
selectRows :: [Int] -> LinSystem -> LinSystem
selectRows is (PolynomialSystem xs) = PolynomialSystem (selectRows' is xs)
selectRows is s@(FpSystem _ _ xs) = s {mijs = selectRows' is xs}
selectRows is s@(FpSolved _ xs _ _) = s {image = selectRows' is xs}
selectRows' :: [Int] -> [a] -> [a]
selectRows' is xs = [xs !! i | i <- is ]

-- | The sparsity pattern of a linear system contains a list of
-- vectors.  Each vector represents one row, and each entry marks a
-- non-zero entry in that row.
sparsityPattern :: LinSystem -> [V.Vector Int]
sparsityPattern (PolynomialSystem xs) = map (V.convert . BV.map fst) xs
sparsityPattern (FpSystem _ _ xs) = map (V.convert . BV.map fst) xs
sparsityPattern (FpSolved _ xs _ _) = map (V.map fst) xs


-- | A scalar integral is represented by its indices.
newtype SInt = SInt (V.Vector Int) deriving Eq
instance Show SInt where
  show (SInt xs) = "Int[" ++ intercalate "," (map show $ V.toList xs) ++ "]"

-- | Scalar integrals are ordered as in Laporta's paper
-- (arXiv:hep-ph/0102033, Algorithm 1, step 9b), in descending order.
instance Ord SInt where
  compare (SInt x) (SInt y) = laportaOrdering y x where
    laportaOrdering :: V.Vector Int -> V.Vector Int -> Ordering
    laportaOrdering =
      comparing (V.length . V.filter (>0)) -- number of propagators.
      <> comparing (numDots . SInt) -- total number of dots.
      <> comparing (numSPs . SInt) -- total number of scalar products.
      <> compareMissingProps -- comapre which propagators are present/absent.
      <> comparePropPowers -- compare powers of individual propagators.
      <> compareSpPowers -- compare powers of individual scalar products.
    compareMissingProps xs ys = mconcat (zipWith (\ a b -> compare (signum (max a 0)) (signum (max b 0))) (V.toList ys) (V.toList xs))
    comparePropPowers xs ys = mconcat (zipWith (\ a b -> compare (max a 0) (max b 0)) (V.toList xs) (V.toList ys))
    compareSpPowers xs ys = mconcat (zipWith (\ a b -> compare (max (- a) 0) (max (- b) 0)) (V.toList xs) (V.toList ys))

-- | The total number of dots of an integral.
numDots :: SInt -> Int
numDots (SInt xs) = V.sum . V.map (+ (-1)) . V.filter (>0) $ xs

-- | The total number of scalar products of an integral.
numSPs :: SInt -> Int
numSPs (SInt xs) = - (V.sum . V.filter (<0) $ xs)

-- | Check whether an integral has more dots and/or scalar products
-- than allowed.
isBeyond :: Config -> SInt -> Bool
isBeyond c (SInt xs) = r > rMax c || s > sMax c
  where
    r = V.sum . V.map (+ (-1)) . V.filter (>0) $ xs
    s = - (V.sum . V.filter (<0) $ xs)

--  | One term in a polynomial in the kinematic invariants and d
data Term = Term !Integer !(V.Vector Word8) deriving Show
-- | One term in an IBP equation.
data IbpLine a = IbpLine !SInt !a deriving (Show, Functor)
-- | An IBP equation.
newtype Ibp a = Ibp (BV.Vector (IbpLine a)) deriving (Show, Functor)

-- | A multivariate Polynomial.
newtype MPoly = MPoly (BV.Vector Integer, R.Array R.U R.DIM2 Word8) deriving Show

-- | Dummy 'Num' instance for 'MPoly'.  We only need (primitive) addition.
instance Num MPoly where
  (+) (MPoly (!x1,!y1)) (MPoly (!x2,!y2)) =
    MPoly (BV.force $ x1 BV.++ x2, R.computeS $ R.transpose (R.transpose y1 R.++ R.transpose y2))
  (*) =         error "(*) not implemented for multivariate polynomials."
  signum =      error "signum not implemented for multivariate polynomials."
  fromInteger = error "fromInteger not implemented for multivariate polynomials."
  abs =         error "abs not implemented for multivariate polynomials."
  negate =      error "negate not implemented for multivariate polynomials."


type Equation a = BV.Vector (Int, a)

-- | Result of successive Monte Carlo runs.
data TestResult = Unlucky -- ^ We have hit a bad evaluation point and have to discard the result of this run.
                | Restart -- ^ The previous run had a bad evaluation point, and we have to restart.
                | Good !Double -- ^ We have not detected a bad point, and the chance that our result is wrong is less than this.



