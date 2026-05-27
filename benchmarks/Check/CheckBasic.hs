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
      let basicRows =
            filter (\r -> value r "logic" == "basic") rows

      if null basicRows
        then failNow "No rows with logic=basic were found."
        else pure ()

      checkAllPassed basicRows
      checkAllStable basicRows
      checkWitnessAgreement basicRows
      checkWitnessSizes basicRows
      checkPurposeFields basicRows
      checkCoreMetricFields basicRows
      checkRequiredBasicFamilies basicRows
      checkBasicScalingFamilies basicRows
      checkReachabilitySeparators basicRows
      checkMultiStartOneBad basicRows
      checkBasicRescueRows basicRows

      ok ("Checked " ++ show (length basicRows) ++ " Basic benchmark rows.")
      ok "All Basic benchmarks passed."
      ok "All Basic benchmark results were stable."
      ok "Witness results agree with model-checking results."
      ok "Witness-size checks passed where an expected witness size is provided."
      ok "Purpose and parameter fields are present."
      ok "Core metric fields are present and parseable."
      ok "All required Basic benchmark families are present."
      ok "Basic scaling families are present and have parameter metadata."
      ok "Reachability-separator checks passed."
      ok "Multi-start reachability pattern checks passed."
      ok "Basic rescue running-example rows are present and semantically consistent."
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

checkWitnessAgreement :: [Row] -> IO ()
checkWitnessAgreement rows = do
  let bad =
        names
          [ r
          | r <- rows
          , isKnown (value r "witness_agrees")
          , value r "witness_agrees" /= "True"
          ]

  if null bad
    then pure ()
    else failNow ("Some witness results disagree with model-checking results: " ++ intercalate ", " bad)

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

checkCoreMetricFields :: [Row] -> IO ()
checkCoreMetricFields rows = do
  let requiredIntFields =
        [ "states"
        , "actions"
        , "transitions"
        , "formula_size"
        ]

      badIntFields =
        [ value r "name" ++ ":" ++ field
        | r <- rows
        , field <- requiredIntFields
        , not (isNonNegativeInt (value r field))
        ]

      badTime =
        names
          [ r
          | r <- rows
          , not (isNonNegativeNumber (value r "time_ms"))
          ]

  if null badIntFields && null badTime
    then pure ()
    else failNow
      ( "Some Basic rows have missing or non-numeric core metrics. Bad integer fields: "
        ++ intercalate ", " badIntFields
        ++ ". Bad time_ms rows: "
        ++ intercalate ", " badTime
      )

checkRequiredBasicFamilies :: [Row] -> IO ()
checkRequiredBasicFamilies rows =
  checkRequiredFamilies rows
    [ "manual-empty-plan"
    , "manual-vacuous-precondition"
    , "manual-reliable-plan"
    , "manual-nondet-success"
    , "manual-multistart-success"
    , "manual-trap-failure"
    , "manual-dead-end-failure"
    , "robot-corridor-safe-plan"
    , "robot-corridor-risky-only"
    , "robot-corridor-multistart"
    , "rescue-basic"
    , "line-positive"
    , "line-broken-negative"
    , "branching-depth-safe-positive"
    , "branching-depth-trap-negative"
    , "branching-width-safe-positive"
    , "branching-width-trap-negative"
    , "multi-start-all-good"
    , "multi-start-one-bad"
    , "action-count-good-last"
    , "action-count-no-good"
    , "path-length-good-last"
    , "path-length-no-good"
    , "trap-reachable-negative"
    , "formula-depth-positive"
    ]

checkRequiredFamilies :: [Row] -> [String] -> IO ()
checkRequiredFamilies rows requiredFamilies = do
  let presentFamilies =
        nub [value r "family" | r <- rows]

      missing =
        [f | f <- requiredFamilies, f `notElem` presentFamilies]

  if null missing
    then pure ()
    else failNow
      ("Missing Basic families: " ++ intercalate ", " missing)

checkBasicScalingFamilies :: [Row] -> IO ()
checkBasicScalingFamilies rows = do
  checkScalingRows "states"
    [ "line-positive"
    , "line-broken-negative"
    , "trap-reachable-negative"
    ]

  checkScalingRows "depth"
    [ "branching-depth-safe-positive"
    , "branching-depth-trap-negative"
    ]

  checkScalingRows "width"
    [ "branching-width-safe-positive"
    , "branching-width-trap-negative"
    ]

  checkScalingRows "actions"
    [ "action-count-good-last"
    , "action-count-no-good"
    ]

  checkScalingRows "path_length"
    [ "path-length-good-last"
    , "path-length-no-good"
    ]

  checkScalingRows "formula_depth"
    [ "formula-depth-positive"
    ]

  where
    checkScalingRows :: String -> [String] -> IO ()
    checkScalingRows parameterName families = do
      let scalingRows =
            [ r
            | r <- rows
            , value r "family" `elem` families
            ]

          badParameter =
            names
              [ r
              | r <- scalingRows
              , value r "primary_parameter" /= parameterName
                 || not (isKnown (value r "parameter_value"))
              ]

      if null scalingRows
        then failNow
          ( "No Basic scaling rows found for parameter="
            ++ parameterName
            ++ "."
          )
        else pure ()

      if null badParameter
        then pure ()
        else failNow
          ( "Some Basic scaling rows have wrong/missing parameter metadata for parameter="
            ++ parameterName
            ++ ": "
            ++ intercalate ", " badParameter
          )

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

  if null checked
    then failNow "No Basic reachability-separator rows were found."
    else pure ()

  if null bad
    then pure ()
    else failNow
      ( "Some intended Basic reachability separators are not ordinary-reachable: "
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

  if null checked
    then failNow "No Basic multi-start-one-bad rows were found."
    else pure ()

  if null bad
    then pure ()
    else failNow
      ( "Some multi-start-one-bad rows do not show the intended reachability pattern: "
        ++ intercalate ", " bad
      )

checkBasicRescueRows :: [Row] -> IO ()
checkBasicRescueRows rows = do
  let required =
        [ ("basic-rescue-safe-route-positive", "True")
        , ("basic-rescue-risky-branch-negative", "False")
        , ("basic-rescue-multistart-positive", "True")
        , ("basic-rescue-dead-end-negative", "False")
        ]

      positiveWitnesses =
        [ ("basic-rescue-safe-route-positive", "3")
        , ("basic-rescue-multistart-positive", "3")
        ]

      negativeSeparators =
        [ "basic-rescue-risky-branch-negative"
        , "basic-rescue-dead-end-negative"
        ]

      rowsByName name =
        [ r | r <- rows, value r "name" == name ]

      missing =
        [ name
        | (name, _) <- required
        , null (rowsByName name)
        ]

      wrong =
        [ name
        | (name, expectedValue) <- required
        , r <- rowsByName name
        , value r "logic" /= "basic"
           || value r "family" /= "rescue-basic"
           || value r "expected" /= expectedValue
           || value r "result" /= expectedValue
           || value r "passed" /= "True"
           || value r "stable" /= "True"
        ]

      badPositiveWitness =
        [ value r "name"
        | (name, size) <- positiveWitnesses
        , r <- rowsByName name
        , value r "witness_found" /= "True"
           || value r "witness_size" /= size
           || value r "witness_size_passed" /= "True"
        ]

      badNegativeSeparator =
        [ value r "name"
        | name <- negativeSeparators
        , r <- rowsByName name
        , value r "ordinary_reachable" /= "True"
           || value r "witness_found" /= "False"
        ]

  if null missing
     && null wrong
     && null badPositiveWitness
     && null badNegativeSeparator
    then pure ()
    else failNow
      ( "Basic rescue running-example checks failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong result/metadata: "
        ++ intercalate ", " wrong
        ++ ". Bad positive witness: "
        ++ intercalate ", " badPositiveWitness
        ++ ". Bad negative separator: "
        ++ intercalate ", " badNegativeSeparator
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

isNonNegativeInt :: String -> Bool
isNonNegativeInt x =
  case reads x :: [(Int, String)] of
    [(n, "")] -> n >= 0
    _         -> False

isNonNegativeNumber :: String -> Bool
isNonNegativeNumber x =
  case reads x :: [(Double, String)] of
    [(n, "")] -> n >= 0
    _         -> False

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