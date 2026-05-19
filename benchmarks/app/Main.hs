module Main where

import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)

import Bench.Basic (basicBenchmarks)
import Bench.Budget (budgetBenchmarks)
import Bench.Common
import Bench.Intermediate (intermediateBenchmarks)
import Bench.Regular (regularBenchmarks)

main :: IO ()
main = do
  args <- getArgs
  let mode = parseMode args
      outFile = parseOut mode args
      suite = parseSuite args
      cases = filter (wantedSuite suite) (allBenchmarks mode)
  createDirectoryIfMissing True "benchmarks/results/raw"
  putStrLn ("Running " ++ show (length cases) ++ " benchmark cases...")
  results <- mapM runOne cases
  writeFile outFile (unlines (csvHeader : map csvRow results))
  putStrLn ("Wrote CSV file to " ++ outFile)

allBenchmarks :: BenchMode -> [BenchCase]
allBenchmarks mode = concat
  [ basicBenchmarks mode
  , intermediateBenchmarks mode
  , regularBenchmarks mode
  , budgetBenchmarks mode
  ]

parseMode :: [String] -> BenchMode
parseMode args
  | "--full" `elem` args = Full
  | otherwise            = Quick

parseOut :: BenchMode -> [String] -> FilePath
parseOut mode args =
  case lookupFlag "--out" args of
    Just path -> path
    Nothing   -> defaultOutput mode

parseSuite :: [String] -> String
parseSuite args =
  case lookupFlag "--suite" args of
    Just s  -> s
    Nothing -> "all"

lookupFlag :: String -> [String] -> Maybe String
lookupFlag _ [] = Nothing
lookupFlag flag (x:y:rest)
  | x == flag = Just y
  | otherwise = lookupFlag flag (y:rest)
lookupFlag _ [_] = Nothing

wantedSuite :: String -> BenchCase -> Bool
wantedSuite "all" _ = True
wantedSuite suite c = suite == caseLogic c || suite == caseFamily c
