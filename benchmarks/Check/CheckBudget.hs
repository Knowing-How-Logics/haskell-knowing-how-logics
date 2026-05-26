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
      let budgetRows =
            filter (\r -> value r "logic" == "budget") rows

      if null budgetRows
        then failNow "No rows with logic=budget were found."
        else pure ()

      checkAllPassed budgetRows
      checkAllStable budgetRows
      checkPurposeFields budgetRows
      checkWitnessSizes budgetRows
      checkRequiredFamilies budgetRows
      checkManualCases budgetRows
      checkReachabilitySeparators budgetRows
      checkBudgetNegativeCases budgetRows
      checkVectorCases budgetRows
      checkRescueCases budgetRows
      checkFormulaDepth budgetRows

      ok ("Checked " ++ show (length budgetRows) ++ " Budget benchmark rows.")
      ok "All Budget benchmarks passed."
      ok "All Budget benchmark results were stable."
      ok "Witness-size checks passed where an expected witness size is provided."
      ok "Required Budget benchmark families are present."
      ok "Budget and vector-budget negative cases passed."
      ok "Budget rescue case-study checks passed."
      ok "Budget benchmark CSV looks consistent."

checkAllPassed :: [Row] -> IO ()
checkAllPassed rows = do
  let bad =
        names [r | r <- rows, value r "passed" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Budget benchmarks did not pass: " ++ intercalate ", " bad)

checkAllStable :: [Row] -> IO ()
checkAllStable rows = do
  let bad =
        names [r | r <- rows, value r "stable" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Budget benchmarks were not stable: " ++ intercalate ", " bad)

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
    else failNow ("Some Budget rows are missing purpose/parameter fields: " ++ intercalate ", " bad)

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
    else failNow ("Some Budget witnesses have unexpected automaton size: " ++ intercalate ", " bad)

checkRequiredFamilies :: [Row] -> IO ()
checkRequiredFamilies rows = do
  let requiredFamilies =
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

      presentFamilies =
        nub [value r "family" | r <- rows]

      missing =
        [f | f <- requiredFamilies, f `notElem` presentFamilies]

  if null missing
    then pure ()
    else failNow ("Missing Budget benchmark families: " ++ intercalate ", " missing)

checkManualCases :: [Row] -> IO ()
checkManualCases rows = do
  let required =
        [ ("budget-manual-empty-plan", "True")
        , ("budget-manual-vacuous-precondition", "True")
        , ("budget-manual-within-budget", "True")
        , ("budget-manual-over-budget", "False")
        , ("budget-manual-unaware-cheap-action", "False")
        , ("budget-vector-manual-within-budget", "True")
        , ("budget-vector-manual-first-dim-failure", "False")
        , ("budget-vector-manual-second-dim-failure", "False")
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
      ( "Manual Budget cases failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong: "
        ++ intercalate ", " wrong
      )

checkReachabilitySeparators :: [Row] -> IO ()
checkReachabilitySeparators rows = do
  let separatorFamilies =
        [ "manual-over-budget"
        , "manual-unaware-cheap-action"
        , "delivery-expensive-only"
        , "robot-time-energy-negative"
        , "rescue-budget"
        , "line-over-budget"
        , "threshold"
        , "cost-per-step-negative"
        , "vector-line-over-budget"
        , "vector-dimension-negative"
        , "vector-tightness"
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
      ( "Some Budget reachability separators are not ordinary-reachable: "
        ++ intercalate ", " bad
      )

checkBudgetNegativeCases :: [Row] -> IO ()
checkBudgetNegativeCases rows = do
  let bad =
        names
          [ r
          | r <- rows
          , value r "family" `elem`
              [ "line-over-budget"
              , "cost-per-step-negative"
              , "class-count-no-good"
              , "manual-over-budget"
              , "manual-unaware-cheap-action"
              ]
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "witness_found" /= "False"
          ]

  if null bad
    then pure ()
    else failNow ("Some 1D budget negative cases failed: " ++ intercalate ", " bad)

checkVectorCases :: [Row] -> IO ()
checkVectorCases rows = do
  let vectorRows =
        [ r
        | r <- rows
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

      badDimension =
        names
          [ r
          | r <- vectorRows
          , value r "budget_dimension" == "NA"
          ]

      badNegative =
        names
          [ r
          | r <- vectorRows
          , value r "expected" == "False"
          , value r "result" /= "False" || value r "witness_found" /= "False"
          ]

  if null vectorRows
    then failNow "No vector-budget rows were found."
    else pure ()

  if null badDimension
    then pure ()
    else failNow ("Some vector-budget rows do not record budget_dimension: " ++ intercalate ", " badDimension)

  if null badNegative
    then pure ()
    else failNow ("Some vector-budget negative rows failed: " ++ intercalate ", " badNegative)


checkRescueCases :: [Row] -> IO ()
checkRescueCases rows = do
  let required =
        [ ("budget-rescue-time-energy-positive", "True")
        , ("budget-rescue-oxygen-negative", "False")
        , ("budget-rescue-detour-within-budget-positive", "True")
        , ("budget-rescue-detour-over-budget-negative", "False")
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

      badPositiveWitness =
        names
          [ r
          | r <- rows
          , (value r "name", value r "witness_size") `elem`
              [ ("budget-rescue-time-energy-positive", "4")
              , ("budget-rescue-detour-within-budget-positive", "5")
              ]
          , value r "witness_found" /= "True"
             || value r "witness_size_passed" /= "True"
             || value r "budget_dimension" /= "2"
          ]

      badPositiveWitnessSize =
        names
          [ r
          | r <- rows
          , value r "name" == "budget-rescue-time-energy-positive"
          , value r "witness_size" /= "4"
          ]
        ++
        names
          [ r
          | r <- rows
          , value r "name" == "budget-rescue-detour-within-budget-positive"
          , value r "witness_size" /= "5"
          ]

      badNegativeSeparator =
        names
          [ r
          | r <- rows
          , value r "name" `elem`
              [ "budget-rescue-oxygen-negative"
              , "budget-rescue-detour-over-budget-negative"
              ]
          , value r "ordinary_reachable" /= "True"
             || value r "witness_found" /= "False"
             || value r "budget_dimension" /= "2"
          ]

  if null missing
      && null wrong
      && null badPositiveWitness
      && null badPositiveWitnessSize
      && null badNegativeSeparator
    then pure ()
    else failNow
      ( "Budget rescue cases failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong: "
        ++ intercalate ", " wrong
        ++ ". Bad positive witness: "
        ++ intercalate ", " badPositiveWitness
        ++ ". Bad positive witness size: "
        ++ intercalate ", " badPositiveWitnessSize
        ++ ". Bad negative separator: "
        ++ intercalate ", " badNegativeSeparator
      )

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
    else failNow ("Some Budget formula-depth rows failed: " ++ intercalate ", " bad)

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