module Main where

import Data.List (intercalate, nub)
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
      let intermediateRows =
            filter (\r -> value r "logic" == "intermediate") rows

      if null intermediateRows
        then failNow "No rows with logic=intermediate were found."
        else pure ()

      checkAllPassed intermediateRows
      checkAllStable intermediateRows
      checkPurposeFields intermediateRows
      checkWitnessSizes intermediateRows
      checkRequiredFamilies intermediateRows
      checkManualCases intermediateRows
      checkReachabilitySeparators intermediateRows
      checkIntermediateConstraintCases intermediateRows
      checkMultiStartCases intermediateRows
      checkFormulaDepth intermediateRows

      ok ("Checked " ++ show (length intermediateRows) ++ " Intermediate benchmark rows.")
      ok "All Intermediate benchmarks passed."
      ok "All Intermediate benchmark results were stable."
      ok "Witness-size checks passed where an expected witness size is provided."
      ok "Required Intermediate benchmark families are present."
      ok "Intermediate reachability-separator and constraint checks passed."
      ok "Intermediate benchmark CSV looks consistent."

checkAllPassed :: [Row] -> IO ()
checkAllPassed rows = do
  let bad =
        names [r | r <- rows, value r "passed" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Intermediate benchmarks did not pass: " ++ intercalate ", " bad)

checkAllStable :: [Row] -> IO ()
checkAllStable rows = do
  let bad =
        names [r | r <- rows, value r "stable" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Intermediate benchmarks were not stable: " ++ intercalate ", " bad)

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
    else failNow ("Some Intermediate rows are missing purpose/parameter fields: " ++ intercalate ", " bad)

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
    else failNow ("Some Intermediate witnesses have unexpected size: " ++ intercalate ", " bad)

checkRequiredFamilies :: [Row] -> IO ()
checkRequiredFamilies rows = do
  let requiredFamilies =
        [ "manual-empty-plan"
        , "manual-vacuous-precondition"
        , "manual-safe-plan"
        , "manual-unsafe-middle-failure"
        , "manual-nondet-safe-success"
        , "manual-nondet-unsafe-failure"
        , "manual-multistart-success"
        , "manual-multistart-one-bad"
        , "manual-dead-end-failure"
        , "robot-safe-corridor"
        , "robot-unsafe-corridor"
        , "robot-risky-branch"
        , "corridor-positive"
        , "corridor-unsafe-middle"
        , "corridor-broken"
        , "branching-depth-safe"
        , "branching-depth-unsafe"
        , "branching-width-safe"
        , "branching-width-unsafe"
        , "multi-start-all-good"
        , "multi-start-one-unsafe"
        , "action-count-safe-last"
        , "action-count-no-safe"
        , "path-length-safe-last"
        , "path-length-unsafe"
        , "formula-depth-positive"
        ]

      presentFamilies =
        nub [value r "family" | r <- rows]

      missing =
        [f | f <- requiredFamilies, f `notElem` presentFamilies]

  if null missing
    then pure ()
    else failNow ("Missing Intermediate benchmark families: " ++ intercalate ", " missing)

checkManualCases :: [Row] -> IO ()
checkManualCases rows = do
  let required =
        [ ("intermediate-manual-empty-plan", "True")
        , ("intermediate-manual-vacuous-precondition", "True")
        , ("intermediate-manual-safe-plan", "True")
        , ("intermediate-manual-unsafe-middle-failure", "False")
        , ("intermediate-manual-nondet-safe-success", "True")
        , ("intermediate-manual-nondet-unsafe-failure", "False")
        , ("intermediate-manual-multistart-success", "True")
        , ("intermediate-manual-multistart-one-bad", "False")
        , ("intermediate-manual-dead-end-failure", "False")
        ]

      missing =
        [ name
        | (name, _) <- required
        , not (any (\r -> value r "name" == name) rows)
        ]

      wrong =
        [ name
        | (name, expectedValue) <- required
        , r <- rows
        , value r "name" == name
        , value r "expected" /= expectedValue || value r "result" /= expectedValue
        ]

  if null missing && null wrong
    then pure ()
    else failNow
      ( "Manual Intermediate cases failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong: "
        ++ intercalate ", " wrong
      )

checkReachabilitySeparators :: [Row] -> IO ()
checkReachabilitySeparators rows = do
  let separatorFamilies =
        [ "manual-unsafe-middle-failure"
        , "manual-nondet-unsafe-failure"
        , "manual-multistart-one-bad"
        , "robot-unsafe-corridor"
        , "robot-risky-branch"
        , "corridor-unsafe-middle"
        , "branching-depth-unsafe"
        , "branching-width-unsafe"
        , "multi-start-one-unsafe"
        , "path-length-unsafe"
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
      ( "Some Intermediate reachability separators are not ordinary-reachable: "
        ++ intercalate ", " bad
      )

checkIntermediateConstraintCases :: [Row] -> IO ()
checkIntermediateConstraintCases rows = do
  let bad =
        names
          [ r
          | r <- rows
          , value r "family" `elem`
              [ "corridor-unsafe-middle"
              , "branching-depth-unsafe"
              , "branching-width-unsafe"
              , "path-length-unsafe"
              ]
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

  if null bad
    then pure ()
    else failNow ("Some intermediate-constraint negative cases failed: " ++ intercalate ", " bad)

checkMultiStartCases :: [Row] -> IO ()
checkMultiStartCases rows = do
  let bad =
        names
          [ r
          | r <- rows
          , value r "family" == "multi-start-one-unsafe"
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "ordinary_all_pre_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

  if null bad
    then pure ()
    else failNow ("Some multi-start-one-unsafe rows failed: " ++ intercalate ", " bad)

checkFormulaDepth :: [Row] -> IO ()
checkFormulaDepth rows = do
  let formulaRows =
        [ r
        | r <- rows
        , value r "family" == "formula-depth-positive"
        ]

      bad =
        names
          [ r
          | r <- formulaRows
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
             || value r "witness_size_passed" /= "True"
          ]

  if null formulaRows
    then failNow "Missing formula-depth-positive rows."
    else pure ()

  if null bad
    then pure ()
    else failNow ("Some Intermediate formula-depth rows failed: " ++ intercalate ", " bad)

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