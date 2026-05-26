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
      let regularRows =
            filter (\r -> value r "logic" == "regular") rows

      if null regularRows
        then failNow "No rows with logic=regular were found."
        else pure ()

      checkAllPassed regularRows
      checkAllStable regularRows
      checkPurposeFields regularRows
      checkWitnessSizes regularRows
      checkRequiredFamilies regularRows
      checkManualCases regularRows
      checkReachabilitySeparators regularRows
      checkAwarenessCases regularRows
      checkMixedClassCases regularRows
      checkRegularLanguageCases regularRows
      checkAutomatonOnlyCases regularRows
      checkAgentDifference regularRows
      checkFormulaDepth regularRows

      ok ("Checked " ++ show (length regularRows) ++ " Regular benchmark rows.")
      ok "All Regular benchmarks passed."
      ok "All Regular benchmark results were stable."
      ok "Witness-size checks passed where an expected witness size is provided."
      ok "Required Regular benchmark families are present."
      ok "Regular reachability-separator checks passed."
      ok "Regular awareness, mixed-class, automaton-only, regular-language, and multi-agent checks passed."
      ok "Regular benchmark CSV looks consistent."

checkAllPassed :: [Row] -> IO ()
checkAllPassed rows = do
  let bad =
        names [r | r <- rows, value r "passed" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Regular benchmarks did not pass: " ++ intercalate ", " bad)

checkAllStable :: [Row] -> IO ()
checkAllStable rows = do
  let bad =
        names [r | r <- rows, value r "stable" /= "True"]

  if null bad
    then pure ()
    else failNow ("Some Regular benchmarks were not stable: " ++ intercalate ", " bad)

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
    else failNow ("Some Regular rows are missing purpose/parameter fields: " ++ intercalate ", " bad)

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
    else failNow ("Some Regular witnesses have unexpected automaton size: " ++ intercalate ", " bad)

checkRequiredFamilies :: [Row] -> IO ()
checkRequiredFamilies rows = do
  let requiredFamilies =
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

      presentFamilies =
        nub [value r "family" | r <- rows]

      missing =
        [f | f <- requiredFamilies, f `notElem` presentFamilies]

  if null missing
    then pure ()
    else failNow ("Missing Regular benchmark families: " ++ intercalate ", " missing)

checkManualCases :: [Row] -> IO ()
checkManualCases rows = do
  let required =
        [ ("regular-manual-empty-plan", "True")
        , ("regular-manual-vacuous-precondition", "True")
        , ("regular-manual-single-good-class", "True")
        , ("regular-manual-good-bad-class", "False")
        , ("regular-manual-not-strongly-executable", "False")
        , ("regular-manual-unaware-good-action", "False")
        , ("regular-manual-agent-one-knows", "True")
        , ("regular-manual-agent-two-fails", "False")
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
      ( "Manual Regular cases failed. Missing: "
        ++ intercalate ", " missing
        ++ ". Wrong: "
        ++ intercalate ", " wrong
      )

checkReachabilitySeparators :: [Row] -> IO ()
checkReachabilitySeparators rows = do
  let separatorFamilies =
        [ "manual-good-bad-class"
        , "manual-not-strongly-executable"
        , "manual-unaware-good-action"
        , "baking-confused-methods"
        , "robot-unaware-safe"
        , "rescue-regular"
        , "automaton-only-size-negative"
        , "mixed-class-negative"
        , "regular-language-width-negative"
        , "regular-language-depth-negative"
        , "basic-capable-unaware-negative"
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
      ( "Some Regular reachability separators are not ordinary-reachable: "
        ++ intercalate ", " bad
      )

checkAwarenessCases :: [Row] -> IO ()
checkAwarenessCases rows = do
  let positiveBad =
        names
          [ r
          | r <- rows
          , value r "family" == "awareness-positive"
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
          ]

      negativeBad =
        names
          [ r
          | r <- rows
          , value r "family" == "basic-capable-unaware-negative"
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "ordinary_all_pre_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

  if null positiveBad && null negativeBad
    then pure ()
    else failNow
      ( "Awareness cases failed. Positive bad: "
        ++ intercalate ", " positiveBad
        ++ ". Negative bad: "
        ++ intercalate ", " negativeBad
      )

checkMixedClassCases :: [Row] -> IO ()
checkMixedClassCases rows = do
  let positiveBad =
        names
          [ r
          | r <- rows
          , value r "family" == "all-good-mixed-class-positive"
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
             || value r "witness_size_passed" /= "True"
          ]

      negativeBad =
        names
          [ r
          | r <- rows
          , value r "family" == "mixed-class-negative"
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

  if null positiveBad && null negativeBad
    then pure ()
    else failNow
      ( "Mixed-class cases failed. Positive bad: "
        ++ intercalate ", " positiveBad
        ++ ". Negative bad: "
        ++ intercalate ", " negativeBad
      )

checkRegularLanguageCases :: [Row] -> IO ()
checkRegularLanguageCases rows = do
  let positiveFamilies =
        [ "regular-language-width-positive"
        , "regular-language-depth-positive"
        ]

      negativeFamilies =
        [ "regular-language-width-negative"
        , "regular-language-depth-negative"
        ]

      positiveBad =
        names
          [ r
          | r <- rows
          , value r "family" `elem` positiveFamilies
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
             || value r "witness_size_passed" /= "True"
          ]

      negativeBad =
        names
          [ r
          | r <- rows
          , value r "family" `elem` negativeFamilies
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

  if null positiveBad && null negativeBad
    then pure ()
    else failNow
      ( "Regular-language cases failed. Positive bad: "
        ++ intercalate ", " positiveBad
        ++ ". Negative bad: "
        ++ intercalate ", " negativeBad
      )

checkAutomatonOnlyCases :: [Row] -> IO ()
checkAutomatonOnlyCases rows = do
  let positiveRows =
        [ r
        | r <- rows
        , value r "family" == "automaton-only-size-positive"
        ]

      negativeRows =
        [ r
        | r <- rows
        , value r "family" == "automaton-only-size-negative"
        ]

      positiveBad =
        names
          [ r
          | r <- positiveRows
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
             || value r "witness_size_passed" /= "True"
          ]

      negativeBad =
        names
          [ r
          | r <- negativeRows
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "ordinary_reachable" /= "True"
             || value r "witness_found" /= "False"
          ]

      positiveStateValues =
        nub [value r "states" | r <- positiveRows]

      negativeStateValues =
        nub [value r "states" | r <- negativeRows]

  if null positiveRows
    then failNow "Missing automaton-only-size-positive rows."
    else pure ()

  if null negativeRows
    then failNow "Missing automaton-only-size-negative rows."
    else pure ()

  if length positiveStateValues == 1
    then pure ()
    else failNow "automaton-only-size-positive does not keep the LTS state count fixed."

  if length negativeStateValues == 1
    then pure ()
    else failNow "automaton-only-size-negative does not keep the LTS state count fixed."

  if null positiveBad && null negativeBad
    then pure ()
    else failNow
      ( "Automaton-only cases failed. Positive bad: "
        ++ intercalate ", " positiveBad
        ++ ". Negative bad: "
        ++ intercalate ", " negativeBad
      )

checkAgentDifference :: [Row] -> IO ()
checkAgentDifference rows = do
  let agentOneRows =
        [ r
        | r <- rows
        , value r "family" == "manual-agent-difference"
        , value r "parameter_value" == "agent-one"
        ]

      agentTwoRows =
        [ r
        | r <- rows
        , value r "family" == "manual-agent-difference"
        , value r "parameter_value" == "agent-two"
        ]

      badAgentOne =
        names
          [ r
          | r <- agentOneRows
          , value r "expected" /= "True"
             || value r "result" /= "True"
             || value r "witness_found" /= "True"
          ]

      badAgentTwo =
        names
          [ r
          | r <- agentTwoRows
          , value r "expected" /= "False"
             || value r "result" /= "False"
             || value r "witness_found" /= "False"
          ]

  if null agentOneRows
    then failNow "Missing regular manual agent-one row."
    else pure ()

  if null agentTwoRows
    then failNow "Missing regular manual agent-two row."
    else pure ()

  if null badAgentOne && null badAgentTwo
    then pure ()
    else failNow
      ( "Agent-difference cases failed. Agent one bad: "
        ++ intercalate ", " badAgentOne
        ++ ". Agent two bad: "
        ++ intercalate ", " badAgentTwo
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
    else failNow ("Some Regular formula-depth rows failed: " ++ intercalate ", " bad)

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