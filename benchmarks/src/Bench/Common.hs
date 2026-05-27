module Bench.Common
  ( BenchMode(..)
  , BenchOutcome(..)
  , BenchCase(..)
  , BenchResult(..)
  , boolOutcome
  , witnessOutcome
  , runOne
  , csvHeader
  , csvRow
  , modeName
  , defaultOutput
  , freshSalt
  , saltOutcome
  ) where

import Control.Exception (evaluate)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.List (sort)
import System.CPUTime (getCPUTime)
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)

data BenchMode = Quick | Full
  deriving (Eq, Show)

data BenchOutcome = BenchOutcome
  { outcomeResult :: Bool
  , outcomeWitnessFound :: Maybe Bool
  , outcomeWitnessSize :: Maybe Int
  , outcomeWitnessAgrees :: Maybe Bool
  , outcomePurpose :: Maybe String
  , outcomePrimaryParameter :: Maybe String
  , outcomeParameterValue :: Maybe String
  , outcomePreStates :: Maybe Int
  , outcomeGoalStates :: Maybe Int
  , outcomeOrdinaryReachable :: Maybe Bool
  , outcomeOrdinaryAllPreReachable :: Maybe Bool
  , outcomeExpectedWitnessSize :: Maybe Int
  , outcomeWitnessSizePassed :: Maybe Bool
  } deriving (Eq, Show)

data BenchCase = BenchCase
  { caseName                 :: String
  , caseLogic                :: String
  , caseFamily               :: String
  , caseMode                 :: BenchMode
  , caseExpected             :: Maybe Bool
  , caseStates               :: Int
  , caseActions              :: Int
  , caseTransitions          :: Int
  , casePropositions         :: Int
  , caseAgents               :: Maybe Int
  , caseAutomata             :: Maybe Int
  , caseAutomatonStates      :: Maybe Int
  , caseAutomatonTransitions :: Maybe Int
  , caseBudgetDim            :: Maybe Int
  , caseFormulaSize          :: Int
  , caseRun                  :: IO BenchOutcome
  }

data BenchResult = BenchResult
  { resultCase       :: BenchCase
  , resultOutcome    :: BenchOutcome
  , resultPassed     :: Maybe Bool
  , resultStable     :: Bool
  , resultSamples    :: Int
  , resultTotalIters :: Int
  , resultMinIters   :: Int
  , resultMaxIters   :: Int
  , resultTimeMs     :: Double
  , resultMinTimeMs  :: Double
  , resultMaxTimeMs  :: Double
  }

saltRef :: IORef Int
saltRef = unsafePerformIO (newIORef 0)
{-# NOINLINE saltRef #-}

freshSalt :: IO Int
freshSalt =
  atomicModifyIORef' saltRef (\n -> let n' = n + 1 in (n', n'))
{-# NOINLINE freshSalt #-}

saltBool :: Int -> Bool -> Bool
saltBool salt value
  | salt == minBound = not value
  | otherwise        = value
{-# NOINLINE saltBool #-}

saltMaybeBool :: Int -> Maybe Bool -> Maybe Bool
saltMaybeBool _ Nothing = Nothing
saltMaybeBool salt (Just value) = Just (saltBool salt value)
{-# NOINLINE saltMaybeBool #-}

saltOutcome :: Int -> BenchOutcome -> BenchOutcome
saltOutcome salt outcome =
  salt `seq` outcome
    { outcomeResult            = saltBool salt (outcomeResult outcome)
    , outcomeWitnessFound      = saltMaybeBool salt (outcomeWitnessFound outcome)
    , outcomeWitnessAgrees     = saltMaybeBool salt (outcomeWitnessAgrees outcome)
    , outcomeWitnessSizePassed = saltMaybeBool salt (outcomeWitnessSizePassed outcome)
    }
{-# NOINLINE saltOutcome #-}

boolOutcome :: Bool -> BenchOutcome
boolOutcome value =
  BenchOutcome
    { outcomeResult                  = value
    , outcomeWitnessFound            = Nothing
    , outcomeWitnessSize             = Nothing
    , outcomeWitnessAgrees           = Nothing
    , outcomePurpose                 = Nothing
    , outcomePrimaryParameter        = Nothing
    , outcomeParameterValue          = Nothing
    , outcomePreStates               = Nothing
    , outcomeGoalStates              = Nothing
    , outcomeOrdinaryReachable       = Nothing
    , outcomeOrdinaryAllPreReachable = Nothing
    , outcomeExpectedWitnessSize     = Nothing
    , outcomeWitnessSizePassed       = Nothing
    }

witnessOutcome :: Bool -> Maybe Int -> BenchOutcome
witnessOutcome value witnessSize =
  (boolOutcome value)
    { outcomeWitnessFound  = Just value
    , outcomeWitnessSize   = witnessSize
    , outcomeWitnessAgrees = Nothing
    }

modeName :: BenchMode -> String
modeName Quick = "quick"
modeName Full  = "full"

defaultOutput :: BenchMode -> FilePath
defaultOutput mode =
  "benchmarks/results/raw/" ++ modeName mode ++ ".csv"

samplesFor :: BenchMode -> Int
samplesFor Quick = 7
samplesFor Full  = 11

targetMsFor :: BenchMode -> Double
targetMsFor Quick = 50.0
targetMsFor Full  = 250.0

maxIterationsFor :: BenchMode -> Int
maxIterationsFor Quick = 200000
maxIterationsFor Full  = 1000000

warmupItersFor :: BenchMode -> Int
warmupItersFor Quick = 10
warmupItersFor Full  = 25

runOne :: BenchCase -> IO BenchResult
runOne c = do
  warmup c (warmupItersFor (caseMode c))
  measurements <- sequence
    [ runSample c
    | _ <- [1 .. samplesFor (caseMode c)]
    ]

  let outcomes     = [o | (o, _, _) <- measurements]
      perIterTimes = [t | (_, t, _) <- measurements]
      iterations   = [i | (_, _, i) <- measurements]
      chosen       = last outcomes
      value        = outcomeResult chosen
      stable       = all (== chosen) outcomes
      passed       = fmap (== value) (caseExpected c)
      sortedTimes  = sort perIterTimes

  pure BenchResult
    { resultCase       = c
    , resultOutcome    = chosen
    , resultPassed     = passed
    , resultStable     = stable
    , resultSamples    = length measurements
    , resultTotalIters = sum iterations
    , resultMinIters   = minimum iterations
    , resultMaxIters   = maximum iterations
    , resultTimeMs     = median sortedTimes
    , resultMinTimeMs  = minimum sortedTimes
    , resultMaxTimeMs  = maximum sortedTimes
    }

warmup :: BenchCase -> Int -> IO ()
warmup _ 0 = pure ()
warmup c n = do
  outcome <- caseRun c >>= forceTimedOutcome
  forceBenchOutcome outcome
  warmup c (n - 1)

runSample :: BenchCase -> IO (BenchOutcome, Double, Int)
runSample c = do
  start <- getCPUTime
  go start 0 Nothing
  where
    mode = caseMode c
    targetMs = targetMsFor mode
    maxIters = maxIterationsFor mode

    go :: Integer -> Int -> Maybe BenchOutcome -> IO (BenchOutcome, Double, Int)
    go start iter lastOutcome = do
      outcome <- caseRun c >>= forceTimedOutcome
      forceBenchOutcome outcome
      now <- getCPUTime
      let iter' = iter + 1
          elapsedMs = picoToMs (now - start)
          done = elapsedMs >= targetMs || iter' >= maxIters

      if done
        then do
          let perIterMs = elapsedMs / fromIntegral iter'
          pure (outcome, perIterMs, iter')
        else go start iter' (Just outcome)

forceTimedOutcome :: BenchOutcome -> IO BenchOutcome
forceTimedOutcome outcome = do
  forceBenchOutcome outcome
  pure outcome

forceBenchOutcome :: BenchOutcome -> IO ()
forceBenchOutcome outcome = do
  _ <- evaluate (outcomeResult outcome)
  forceMaybeBool (outcomeWitnessFound outcome)
  forceMaybeInt (outcomeWitnessSize outcome)
  forceMaybeBool (outcomeWitnessAgrees outcome)
  forceMaybeString (outcomePurpose outcome)
  forceMaybeString (outcomePrimaryParameter outcome)
  forceMaybeString (outcomeParameterValue outcome)
  forceMaybeInt (outcomePreStates outcome)
  forceMaybeInt (outcomeGoalStates outcome)
  forceMaybeBool (outcomeOrdinaryReachable outcome)
  forceMaybeBool (outcomeOrdinaryAllPreReachable outcome)
  forceMaybeInt (outcomeExpectedWitnessSize outcome)
  forceMaybeBool (outcomeWitnessSizePassed outcome)

forceMaybeBool :: Maybe Bool -> IO ()
forceMaybeBool Nothing = pure ()
forceMaybeBool (Just x) = evaluate x >> pure ()

forceMaybeInt :: Maybe Int -> IO ()
forceMaybeInt Nothing = pure ()
forceMaybeInt (Just x) = evaluate x >> pure ()

forceMaybeString :: Maybe String -> IO ()
forceMaybeString Nothing = pure ()
forceMaybeString (Just x) = evaluate (length x) >> pure ()

picoToMs :: Integer -> Double
picoToMs ps =
  fromIntegral ps / 1000000000.0

median :: [Double] -> Double
median [] =
  0.0
median xs =
  let ys = sort xs
      n  = length ys
      h  = n `div` 2
  in if odd n
        then ys !! h
        else ((ys !! (h - 1)) + (ys !! h)) / 2.0

showMaybeInt :: Maybe Int -> String
showMaybeInt Nothing  = "NA"
showMaybeInt (Just x) = show x

showMaybeBool :: Maybe Bool -> String
showMaybeBool Nothing  = "NA"
showMaybeBool (Just x) = show x

showMaybeString :: Maybe String -> String
showMaybeString Nothing  = "NA"
showMaybeString (Just x) = csvCell x

csvHeader :: String
csvHeader = concat
  [ "name,logic,family,mode,"
  , "expected,result,passed,stable,"
  , "samples,total_iterations,min_iterations,max_iterations,"
  , "states,actions,transitions,propositions,"
  , "agents,automata,automaton_states,automaton_transitions,budget_dimension,"
  , "formula_size,"
  , "purpose,primary_parameter,parameter_value,"
  , "pre_states,goal_states,"
  , "ordinary_reachable,ordinary_all_pre_reachable,"
  , "witness_found,witness_size,expected_witness_size,witness_size_passed,witness_agrees,"
  , "time_ms,min_time_ms,max_time_ms"
  ]

csvRow :: BenchResult -> String
csvRow r = concat
  [ csvCell (caseName c), ","
  , csvCell (caseLogic c), ","
  , csvCell (caseFamily c), ","
  , modeName (caseMode c), ","

  , showMaybeBool (caseExpected c), ","
  , show (outcomeResult outcome), ","
  , showMaybeBool (resultPassed r), ","
  , show (resultStable r), ","

  , show (resultSamples r), ","
  , show (resultTotalIters r), ","
  , show (resultMinIters r), ","
  , show (resultMaxIters r), ","

  , show (caseStates c), ","
  , show (caseActions c), ","
  , show (caseTransitions c), ","
  , show (casePropositions c), ","

  , showMaybeInt (caseAgents c), ","
  , showMaybeInt (caseAutomata c), ","
  , showMaybeInt (caseAutomatonStates c), ","
  , showMaybeInt (caseAutomatonTransitions c), ","
  , showMaybeInt (caseBudgetDim c), ","

  , show (caseFormulaSize c), ","

  , showMaybeString (outcomePurpose outcome), ","
  , showMaybeString (outcomePrimaryParameter outcome), ","
  , showMaybeString (outcomeParameterValue outcome), ","

  , showMaybeInt (outcomePreStates outcome), ","
  , showMaybeInt (outcomeGoalStates outcome), ","
  , showMaybeBool (outcomeOrdinaryReachable outcome), ","
  , showMaybeBool (outcomeOrdinaryAllPreReachable outcome), ","

  , showMaybeBool (outcomeWitnessFound outcome), ","
  , showMaybeInt (outcomeWitnessSize outcome), ","
  , showMaybeInt (outcomeExpectedWitnessSize outcome), ","
  , showMaybeBool (outcomeWitnessSizePassed outcome), ","
  , showMaybeBool (outcomeWitnessAgrees outcome), ","

  , printf "%.6f" (resultTimeMs r), ","
  , printf "%.6f" (resultMinTimeMs r), ","
  , printf "%.6f" (resultMaxTimeMs r)
  ]
  where
    c = resultCase r
    outcome = resultOutcome r

csvCell :: String -> String
csvCell s
  | any (`elem` [',', '"', '\n', '\r']) s =
      "\"" ++ concatMap escape s ++ "\""
  | otherwise =
      s
  where
    escape '"' = "\"\""
    escape ch  = [ch]
