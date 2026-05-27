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
      checkLogicExists rows "basic"
      checkLogicExists rows "regular"
      checkLogicExists rows "intermediate"
      checkLogicExists rows "budget"

      checkAllPassed rows
      checkAllStable rows
      checkPurposeFields rows
      checkWitnessSizes rows

      checkRequiredBasicFamilies rows
      checkRequiredRegularFamilies rows
      checkRequiredIntermediateFamilies rows
      checkRequiredBudgetFamilies rows

      checkReachabilitySeparators rows
      checkVectorBudgetRows rows
      checkRescueRunningExampleRows rows

      ok ("Checked " ++ show (length rows) ++ " benchmark rows.")
      ok "All benchmark rows passed."
      ok "All benchmark rows were stable."
      ok "Purpose and parameter fields are present."
      ok "Witness-size checks passed where expected witness sizes are provided."
      ok "All required benchmark families are present."
      ok "Reachability-separator checks passed."
      ok "Vector-budget rows record budget dimensions."
      ok "Autonomous rescue running-example rows are present and semantically consistent."
      ok "Benchmark CSV looks consistent."

checkLogicExists :: [Row] -> String -> IO ()
checkLogicExists rows logicName = do
  let logicRows =
        [r | r <- rows, value r "logic" == logicName]

  if null logicRows
    then failNow ("No rows with logic=" ++ logicName ++ " were found.")
    else ok ("Found " ++ show (length logicRows) ++ " rows for logic=" ++ logicName ++ ".")

checkAllPassed :: [Row] -> IO ()
checkAllPassed rows = do
  let bad =
        names [r | r <- rows, value r "passed" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some benchmarks did not pass: " ++ intercalate ", " bad)

checkAllStable :: [Row] -> IO ()
checkAllStable rows = do
  let bad =
        names [r | r <- rows, value r "stable" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some benchmarks were not stable: " ++ intercalate ", " bad)

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

checkRequiredBasicFamilies :: [Row] -> IO ()
checkRequiredBasicFamilies rows =
  checkRequiredFamilies rows "basic"
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

checkRequiredRegularFamilies :: [Row] -> IO ()
checkRequiredRegularFamilies rows =
  checkRequiredFamilies rows "regular"
    [ "manual-empty-plan"
    , "manual-vacuous-precondition"
    , "manual-single-good-class"
    , "manual-good-bad-class"
    , "manual-not-strongly-executable"
    , "manual-unaware-good-action"
    , "manual-agent-difference"
    , "baking-good-method"
    , "baking-confused-methods"
    , "robot-aware-safe"
    , "robot-unaware-safe"
    , "rescue-regular"
    , "line-positive"
    , "line-broken-negative"
    , "automaton-only-size-positive"
    , "automaton-only-size-negative"
    , "class-count-good-last"
    , "class-count-no-good"
    , "all-good-mixed-class-positive"
    , "mixed-class-negative"
    , "regular-language-width-positive"
    , "regular-language-width-negative"
    , "regular-language-depth-positive"
    , "regular-language-depth-negative"
    , "awareness-positive"
    , "basic-capable-unaware-negative"
    , "multi-agent-one-knows"
    , "multi-agent-last-fails"
    , "formula-depth-positive"
    ]

checkRequiredIntermediateFamilies :: [Row] -> IO ()
checkRequiredIntermediateFamilies rows =
  checkRequiredFamilies rows "intermediate"
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
    , "rescue-intermediate"
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

checkRequiredBudgetFamilies :: [Row] -> IO ()
checkRequiredBudgetFamilies rows =
  checkRequiredFamilies rows "budget"
    [ "manual-empty-plan"
    , "manual-vacuous-precondition"
    , "manual-within-budget"
    , "manual-over-budget"
    , "manual-unaware-cheap-action"
    , "vector-manual-within-budget"
    , "vector-manual-first-dim-failure"
    , "vector-manual-second-dim-failure"
    , "delivery-cheap-route"
    , "delivery-expensive-only"
    , "robot-time-energy-positive"
    , "robot-time-energy-negative"
    , "rescue-budget"
    , "line-positive"
    , "line-over-budget"
    , "threshold"
    , "cost-per-step-positive"
    , "cost-per-step-negative"
    , "class-count-good-last"
    , "class-count-no-good"
    , "vector-line-positive"
    , "vector-line-over-budget"
    , "vector-dimension-positive"
    , "vector-dimension-negative"
    , "vector-tightness"
    , "formula-depth-positive"
    ]

checkRequiredFamilies :: [Row] -> String -> [String] -> IO ()
checkRequiredFamilies rows logicName requiredFamilies = do
  let logicRows =
        [r | r <- rows, value r "logic" == logicName]

      presentFamilies =
        nub [value r "family" | r <- logicRows]

      missing =
        [f | f <- requiredFamilies, f `notElem` presentFamilies]

  if null missing
    then pure ()
    else failNow
      ( "Missing families for logic="
        ++ logicName
        ++ ": "
        ++ intercalate ", " missing
      )

checkReachabilitySeparators :: [Row] -> IO ()
checkReachabilitySeparators rows = do
  let separatorRows =
        [ r
        | r <- rows
        , value r "expected" == "False"
        , value r "ordinary_reachable" == "True"
        ]

  if null separatorRows
    then failNow "No reachability-separator rows were found."
    else ok ("Found " ++ show (length separatorRows) ++ " reachability-separator rows.")

checkVectorBudgetRows :: [Row] -> IO ()
checkVectorBudgetRows rows = do
  let vectorRows =
        [ r
        | r <- rows
        , value r "logic" == "budget"
        , value r "family" `elem`
            [ "vector-manual-within-budget"
            , "vector-manual-first-dim-failure"
            , "vector-manual-second-dim-failure"
            , "robot-time-energy-positive"
            , "robot-time-energy-negative"
            , "rescue-budget"
            , "vector-line-positive"
            , "vector-line-over-budget"
            , "vector-dimension-positive"
            , "vector-dimension-negative"
            , "vector-tightness"
            ]
        ]

      bad =
        names
          [ r
          | r <- vectorRows
          , value r "budget_dimension" == "NA"
          ]

  if null vectorRows
    then failNow "No vector-budget rows were found."
    else pure ()

  if null bad
    then pure ()
    else failNow ("Some vector-budget rows do not record budget_dimension: " ++ intercalate ", " bad)

checkRescueRunningExampleRows :: [Row] -> IO ()
checkRescueRunningExampleRows rows = do
  let required =
        [ ("basic-rescue-safe-route-positive", "basic", "rescue-basic", "True")
        , ("basic-rescue-risky-branch-negative", "basic", "rescue-basic", "False")

        , ("intermediate-rescue-safe-route-positive", "intermediate", "rescue-intermediate", "True")
        , ("intermediate-rescue-smoke-route-negative", "intermediate", "rescue-intermediate", "False")
        , ("intermediate-rescue-risky-branch-negative", "intermediate", "rescue-intermediate", "False")
        , ("intermediate-rescue-blocked-door-detour-positive", "intermediate", "rescue-intermediate", "True")

        , ("regular-rescue-aware-route-positive", "regular", "rescue-regular", "True")
        , ("regular-rescue-confused-routes-negative", "regular", "rescue-regular", "False")
        , ("regular-rescue-unaware-safe-route-negative", "regular", "rescue-regular", "False")
        , ("regular-rescue-alternative-safe-routes-positive", "regular", "rescue-regular", "True")

        , ("budget-rescue-time-energy-positive", "budget", "rescue-budget", "True")
        , ("budget-rescue-oxygen-negative", "budget", "rescue-budget", "False")
        , ("budget-rescue-detour-within-budget-positive", "budget", "rescue-budget", "True")
        , ("budget-rescue-detour-over-budget-negative", "budget", "rescue-budget", "False")
        ]

      positiveWitnesses =
        [ ("basic-rescue-safe-route-positive", "3")
        , ("intermediate-rescue-safe-route-positive", "3")
        , ("intermediate-rescue-blocked-door-detour-positive", "4")
        , ("regular-rescue-aware-route-positive", "4")
        , ("regular-rescue-alternative-safe-routes-positive", "5")
        , ("budget-rescue-time-energy-positive", "4")
        , ("budget-rescue-detour-within-budget-positive", "5")
        ]

      negativeSeparators =
        [ "basic-rescue-risky-branch-negative"
        , "intermediate-rescue-smoke-route-negative"
        , "intermediate-rescue-risky-branch-negative"
        , "regular-rescue-confused-routes-negative"
        , "regular-rescue-unaware-safe-route-negative"
        , "budget-rescue-oxygen-negative"
        , "budget-rescue-detour-over-budget-negative"
        ]

      budgetRows =
        [ "budget-rescue-time-energy-positive"
        , "budget-rescue-oxygen-negative"
        , "budget-rescue-detour-within-budget-positive"
        , "budget-rescue-detour-over-budget-negative"
        ]

      rowsByName name =
        [ r | r <- rows, value r "name" == name ]

      missing =
        [ name
        | (name, _, _, _) <- required
        , null (rowsByName name)
        ]

      wrong =
        [ name
        | (name, logicName, familyName, expectedValue) <- required
        , r <- rowsByName name
        , value r "logic" /= logicName
           || value r "family" /= familyName
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

      badBudgetDimension =
        [ value r "name"
        | name <- budgetRows
        , r <- rowsByName name
        , value r "budget_dimension" /= "2"
        ]

  if null missing
     && null wrong
     && null badPositiveWitness
     && null badNegativeSeparator
     && null badBudgetDimension
    then pure ()
    else failNow
      ( "Autonomous rescue running-example checks failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong result/metadata: "
        ++ intercalate ", " wrong
        ++ ". Bad positive witness: "
        ++ intercalate ", " badPositiveWitness
        ++ ". Bad negative separator: "
        ++ intercalate ", " badNegativeSeparator
        ++ ". Bad budget dimension: "
        ++ intercalate ", " badBudgetDimension
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
