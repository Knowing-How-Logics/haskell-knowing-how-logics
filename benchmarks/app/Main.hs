module Main where

import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)

import Data.List (isPrefixOf)

import Bench.Basic (basicBenchmarks)
import Bench.Budget (budgetBenchmarks)
import Bench.Common
import Bench.Intermediate (intermediateBenchmarks)
import Bench.Random (defaultRandomCases, randomBenchmarks)
import Bench.Regular (regularBenchmarks)

data Options = Options
  { optMode        :: BenchMode
  , optSuite       :: String
  , optOut         :: Maybe FilePath
  , optRandomCases :: Int
  , optSeed        :: Int
  }

main :: IO ()
main = do
  args <- getArgs

  case parseArgs defaultOptions args of
    Left err -> do
      putStrLn ("Error: " ++ err)
      putStrLn usage
      exitFailure

    Right opts -> do
      let mode =
            optMode opts

          outFile =
            case optOut opts of
              Just path -> path
              Nothing   -> defaultOutput mode

          suite =
            optSuite opts

          requestedRandomSuite =
            suite == "random" || "random-" `isPrefixOf` suite

          randomCount =
            if optRandomCases opts > 0
               then optRandomCases opts
               else if requestedRandomSuite
                    then defaultRandomCases mode
                    else 0

          cases =
            filter (wantedSuite suite)
              (allBenchmarks mode ++ randomBenchmarks mode (optSeed opts) randomCount)

      if null cases
        then do
          putStrLn ("Error: no benchmark cases matched suite: " ++ suite)
          putStrLn usage
          exitFailure
        else pure ()

      createDirectoryIfMissing True (takeDirectory outFile)

      putStrLn ("Running " ++ show (length cases) ++ " benchmark cases...")
      putStrLn ("mode=" ++ modeName mode)
      putStrLn ("suite=" ++ suite)
      putStrLn ("seed=" ++ show (optSeed opts))
      putStrLn ("random_cases_per_logic=" ++ show randomCount)
      putStrLn ("output=" ++ outFile)

      results <- mapM runOne cases

      writeFile outFile (unlines (csvHeader : map csvRow results))

      putStrLn ("Wrote CSV file to " ++ outFile)

defaultOptions :: Options
defaultOptions =
  Options
    { optMode = Quick
    , optSuite = "all"
    , optOut = Nothing
    , optRandomCases = 0
    , optSeed = 20260529
    }

parseArgs :: Options -> [String] -> Either String Options
parseArgs opts [] =
  Right opts

parseArgs opts ("--quick" : rest) =
  parseArgs opts { optMode = Quick } rest

parseArgs opts ("--full" : rest) =
  parseArgs opts { optMode = Full } rest

parseArgs opts ("--suite" : value : rest)
  | isFlag value =
      Left "--suite expects a value, but got another flag."

  | otherwise =
      parseArgs opts { optSuite = value } rest

parseArgs _ ["--suite"] =
  Left "--suite expects a value."

parseArgs opts ("--out" : value : rest)
  | isFlag value =
      Left "--out expects a file path, but got another flag."

  | otherwise =
      parseArgs opts { optOut = Just value } rest

parseArgs _ ["--out"] =
  Left "--out expects a file path."

parseArgs opts ("--random" : value : rest)
  | isFlag value =
      Left "--random expects a non-negative integer, but got another flag."

  | otherwise =
      case reads value of
        [(n, "")] | n >= 0 ->
          parseArgs opts { optRandomCases = n } rest
        _ ->
          Left "--random expects a non-negative integer."

parseArgs _ ["--random"] =
  Left "--random expects a non-negative integer."

parseArgs opts ("--seed" : value : rest)
  | isFlag value =
      Left "--seed expects an integer, but got another flag."

  | otherwise =
      case reads value of
        [(seed, "")] ->
          parseArgs opts { optSeed = seed } rest
        _ ->
          Left "--seed expects an integer."

parseArgs _ ["--seed"] =
  Left "--seed expects an integer."

parseArgs _ (unknown : _) =
  Left ("unknown argument: " ++ unknown)

isFlag :: String -> Bool
isFlag ('-' : '-' : _) =
  True
isFlag _ =
  False

usage :: String
usage =
  unlines
    [ "Usage:"
    , "  stack exec khora-bench -- [--quick|--full] [--suite SUITE] [--out FILE] [--random N] [--seed SEED]"
    , ""
    , "Examples:"
    , "  stack exec khora-bench -- --quick"
    , "  stack exec khora-bench -- --full"
    , "  stack exec khora-bench -- --full --suite basic"
    , "  stack exec khora-bench -- --full --suite regular"
    , "  stack exec khora-bench -- --full --suite rescue-basic"
    , "  stack exec khora-bench -- --full --suite rescue-regular"
    , "  stack exec khora-bench -- --full --suite rescue-intermediate"
    , "  stack exec khora-bench -- --full --suite rescue-budget"
    , "  stack exec khora-bench -- --full --suite regular --out benchmarks/results/raw/regular-full.csv"
    , "  stack exec khora-bench -- --quick --suite random --random 20 --seed 20260529"
    , "  stack exec khora-bench -- --quick --suite basic --random 10"
    , ""
    , "Available suites:"
    , "  all"
    , "  basic"
    , "  intermediate"
    , "  regular"
    , "  budget"
    , "  random"
    , "  random-basic"
    , "  random-intermediate"
    , "  random-regular"
    , "  random-budget"
    , "  or any family name, such as line-positive, awareness-positive, trap-reachable-negative,"
    , "  rescue-basic, rescue-regular, rescue-intermediate, rescue-budget"
    ]

allBenchmarks :: BenchMode -> [BenchCase]
allBenchmarks mode =
  concat
    [ basicBenchmarks mode
    , intermediateBenchmarks mode
    , regularBenchmarks mode
    , budgetBenchmarks mode
    ]

wantedSuite :: String -> BenchCase -> Bool
wantedSuite "all" _ =
  True
wantedSuite "random" c =
  "random-" `isPrefixOf` caseFamily c
wantedSuite suite c =
  suite == caseLogic c || suite == caseFamily c
