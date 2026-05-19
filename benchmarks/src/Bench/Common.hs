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
  ) where

import Control.Exception (evaluate)
import Data.List (sort)
import Text.Printf (printf)
import System.CPUTime (getCPUTime)

data BenchMode = Quick | Full
  deriving (Eq, Show)

data BenchOutcome = BenchOutcome
  { outcomeResult                  :: Bool
  , outcomeWitnessFound            :: Maybe Bool
  , outcomeWitnessSize             :: Maybe Int
  , outcomePurpose                 :: Maybe String
  , outcomePrimaryParameter        :: Maybe String
  , outcomeParameterValue          :: Maybe String
  , outcomePreStates               :: Maybe Int
  , outcomeGoalStates              :: Maybe Int
  , outcomeOrdinaryReachable       :: Maybe Bool
  , outcomeOrdinaryAllPreReachable :: Maybe Bool
  , outcomeExpectedWitnessSize     :: Maybe Int
  , outcomeWitnessSizePassed       :: Maybe Bool
  } deriving (Eq, Show)

data BenchCase = BenchCase
  { caseName            :: String
  , caseLogic           :: String
  , caseFamily          :: String
  , caseMode            :: BenchMode
  , caseExpected        :: Maybe Bool
  , caseStates          :: Int
  , caseActions         :: Int
  , caseTransitions     :: Int
  , casePropositions    :: Int
  , caseAgents          :: Maybe Int
  , caseAutomata        :: Maybe Int
  , caseAutomatonStates :: Maybe Int
  , caseBudgetDim       :: Maybe Int
  , caseFormulaSize     :: Int
  , caseRun             :: IO BenchOutcome
  }

data BenchResult = BenchResult
  { resultCase          :: BenchCase
  , resultOutcome       :: BenchOutcome
  , resultPassed        :: Maybe Bool
  , resultStable        :: Bool
  , resultSamples       :: Int
  , resultTotalIters    :: Int
  , resultMinIters      :: Int
  , resultMaxIters      :: Int
  , resultTimeMs        :: Double
  , resultMinTimeMs     :: Double
  , resultMaxTimeMs     :: Double
  }

boolOutcome :: Bool -> BenchOutcome
boolOutcome value =
  BenchOutcome
    { outcomeResult                  = value
    , outcomeWitnessFound            = Nothing
    , outcomeWitnessSize             = Nothing
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
    { outcomeWitnessFound = Just value
    , outcomeWitnessSize  = witnessSize
    }

modeName :: BenchMode -> String
modeName Quick = "quick"
modeName Full  = "full"

defaultOutput :: BenchMode -> FilePath
defaultOutput mode =
  "benchmarks/results/raw/" ++ modeName mode ++ ".csv"

samplesFor :: BenchMode -> Int
samplesFor Quick = 3
samplesFor Full  = 5

targetMsFor :: BenchMode -> Double
targetMsFor Quick = 5.0
targetMsFor Full  = 25.0

maxIterationsFor :: BenchMode -> Int
maxIterationsFor Quick = 1000
maxIterationsFor Full  = 10000

runOne :: BenchCase -> IO BenchResult
runOne c = do
  measurements <- sequence
    [ runSample c
    | _ <- [1 .. samplesFor (caseMode c)]
    ]

  let outcomes      = [o | (o, _, _) <- measurements]
      perIterTimes  = [t | (_, t, _) <- measurements]
      iterations    = [i | (_, _, i) <- measurements]
      chosen        = last outcomes
      value         = outcomeResult chosen
      stable        = all (== chosen) outcomes
      passed        = fmap (== value) (caseExpected c)
      sortedTimes   = sort perIterTimes

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

runSample :: BenchCase -> IO (BenchOutcome, Double, Int)
runSample c = do
  start <- getCPUTime
  go start 0
  where
    mode = caseMode c
    targetMs = targetMsFor mode
    maxIters = maxIterationsFor mode

    go :: Integer -> Int -> IO (BenchOutcome, Double, Int)
    go start iter = do
      outcome <- caseRun c >>= forceTimedOutcome
      now <- getCPUTime
      let iter' = iter + 1
          elapsedMs = picoToMs (now - start)

      if elapsedMs >= targetMs || iter' >= maxIters
        then do
          let perIterMs = elapsedMs / fromIntegral iter'
          pure (outcome, perIterMs, iter')
        else go start iter'

forceTimedOutcome :: BenchOutcome -> IO BenchOutcome
forceTimedOutcome outcome = do
  _ <- evaluate (outcomeResult outcome)
  _ <- evaluate (outcomeWitnessFound outcome)
  _ <- evaluate (outcomeWitnessSize outcome)
  pure outcome

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
  , "agents,automata,automaton_states,budget_dimension,"
  , "formula_size,"
  , "purpose,primary_parameter,parameter_value,"
  , "pre_states,goal_states,"
  , "ordinary_reachable,ordinary_all_pre_reachable,"
  , "witness_found,witness_size,expected_witness_size,witness_size_passed,"
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

  , printf "%.3f" (resultTimeMs r), ","
  , printf "%.3f" (resultMinTimeMs r), ","
  , printf "%.3f" (resultMaxTimeMs r)
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