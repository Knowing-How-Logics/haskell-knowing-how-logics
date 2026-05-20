module Main where

import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeDirectory)

import Bench.Basic (basicBenchmarks)
import Bench.Budget (budgetBenchmarks)
import Bench.Common
import Bench.Intermediate (intermediateBenchmarks)
import Bench.Regular (regularBenchmarks)

data Options = Options
  { optMode  :: BenchMode
  , optSuite :: String
  , optOut   :: Maybe FilePath
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

          cases =
            filter (wantedSuite suite) (allBenchmarks mode)

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
    , "  stack run khora-bench -- [--quick|--full] [--suite SUITE] [--out FILE]"
    , ""
    , "Examples:"
    , "  stack run khora-bench -- --quick"
    , "  stack run khora-bench -- --full"
    , "  stack run khora-bench -- --full --suite basic"
    , "  stack run khora-bench -- --full --suite regular"
    , "  stack run khora-bench -- --full --suite regular --out benchmarks/results/raw/full.csv"
    , ""
    , "Available suites:"
    , "  all"
    , "  basic"
    , "  intermediate"
    , "  regular"
    , "  budget"
    , "  or any family name, such as line-positive, awareness-negative, trap-reachable-negative"
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
wantedSuite suite c =
  suite == caseLogic c || suite == caseFamily c