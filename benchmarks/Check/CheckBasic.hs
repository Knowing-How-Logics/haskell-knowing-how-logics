module Main where

import Data.List (intercalate)
import System.Environment (getArgs)
import System.Exit (exitFailure)

type Row = [(String, String)]

main :: IO ()
main = do
  args <- getArgs
  let path =
        case args of
          []    -> "benchmarks/results/raw/full.csv"
          (x:_) -> x

  content <- readFile path

  case parseCSV content of
    Left err ->
      failNow ("CSV parse error: " ++ err)

    Right rows -> do
      let basicRows =
            filter (\r -> value r "logic" == "basic") rows

      if null basicRows
        then failNow "No rows with logic=basic were found."
        else pure ()

      checkAllPassed basicRows
      checkAllStable basicRows
      checkWitnessSizes basicRows
      checkPurposeFields basicRows
      checkReachabilitySeparators basicRows
      checkMultiStartOneBad basicRows

      ok ("Checked " ++ show (length basicRows) ++ " Basic benchmark rows.")
      ok "All Basic benchmarks passed."
      ok "All Basic benchmark results were stable."
      ok "Witness-size checks passed where an expected witness size is provided."
      ok "Reachability-separator checks passed."
      ok "Basic benchmark CSV looks consistent."

checkAllPassed :: [Row] -> IO ()
checkAllPassed rows = do
  let bad =
        names [r | r <- rows, value r "passed" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Basic benchmarks did not pass: " ++ intercalate ", " bad)

checkAllStable :: [Row] -> IO ()
checkAllStable rows = do
  let bad =
        names [r | r <- rows, value r "stable" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Basic benchmarks were not stable: " ++ intercalate ", " bad)

checkWitnessSizes :: [Row] -> IO ()
checkWitnessSizes rows = do
  let checked =
        [ r
        | r <- rows
        , isKnown (value r "expected_witness_size")
        ]

      bad =
        names
          [ r
          | r <- checked
          , value r "witness_size_passed" /= "True"
          ]

  if null bad
    then pure ()
    else failNow ("Some witnesses have unexpected size: " ++ intercalate ", " bad)

checkPurposeFields :: [Row] -> IO ()
checkPurposeFields rows = do
  let bad =
        names
          [ r
          | r <- rows
          , not (isKnown (value r "purpose"))
             || not (isKnown (value r "primary_parameter"))
             || not (isKnown (value r "parameter_value"))
          ]

  if null bad
    then pure ()
    else failNow ("Some rows are missing purpose/parameter fields: " ++ intercalate ", " bad)

checkReachabilitySeparators :: [Row] -> IO ()
checkReachabilitySeparators rows = do
  let separatorFamilies =
        [ "manual-trap-failure"
        , "robot-corridor-risky-only"
        , "trap-reachable-negative"
        , "branching-depth-trap-negative"
        , "branching-width-trap-negative"
        , "rescue-basic"
        ]

      checked =
        [ r
        | r <- rows
        , value r "family" `elem` separatorFamilies
        , value r "expected" == "False"
        ]

      bad =
        names
          [ r
          | r <- checked
          , value r "ordinary_reachable" /= "True"
          ]

  if null bad
    then pure ()
    else failNow
      ( "Some intended reachability separators are not ordinary-reachable: "
        ++ intercalate ", " bad
      )

checkMultiStartOneBad :: [Row] -> IO ()
checkMultiStartOneBad rows = do
  let checked =
        [ r
        | r <- rows
        , value r "family" == "multi-start-one-bad"
        ]

      bad =
        names
          [ r
          | r <- checked
          , value r "ordinary_reachable" /= "True"
             || value r "ordinary_all_pre_reachable" /= "False"
          ]

  if null bad
    then pure ()
    else failNow
      ( "Some multi-start-one-bad rows do not show the intended reachability pattern: "
        ++ intercalate ", " bad
      )

names :: [Row] -> [String]
names =
  map (\r -> value r "name")

value :: Row -> String -> String
value row key =
  case lookup key row of
    Just x  -> x
    Nothing -> ""

isKnown :: String -> Bool
isKnown x =
  not (x == "" || x == "NA")

ok :: String -> IO ()
ok msg =
  putStrLn ("[OK] " ++ msg)

failNow :: String -> IO a
failNow msg = do
  putStrLn ("[FAIL] " ++ msg)
  exitFailure

parseCSV :: String -> Either String [Row]
parseCSV content =
  case mapM parseLine cleanLines of
    Left err ->
      Left err

    Right [] ->
      Left "empty CSV file"

    Right (header:records) ->
      mapM (mkRow header) records
  where
    cleanLines =
      filter (not . null) (map stripCR (lines content))

mkRow :: [String] -> [String] -> Either String Row
mkRow header record
  | length header == length record =
      Right (zip header record)

  | otherwise =
      Left
        ( "row has "
          ++ show (length record)
          ++ " fields, but header has "
          ++ show (length header)
          ++ " fields"
        )

stripCR :: String -> String
stripCR =
  filter (/= '\r')

parseLine :: String -> Either String [String]
parseLine input =
  go [] [] False input
  where
    go :: [String] -> String -> Bool -> String -> Either String [String]
    go fields field inQuotes rest =
      case rest of
        [] ->
          if inQuotes
            then Left "unterminated quoted field"
            else Right (reverse (reverse field : fields))

        ',' : xs ->
          if inQuotes
            then go fields (',' : field) inQuotes xs
            else go (reverse field : fields) [] inQuotes xs

        '"' : '"' : xs ->
          if inQuotes
            then go fields ('"' : field) inQuotes xs
            else go fields ('"' : '"' : field) inQuotes xs

        '"' : xs ->
          go fields field (not inQuotes) xs

        x : xs ->
          go fields (x : field) inQuotes xs