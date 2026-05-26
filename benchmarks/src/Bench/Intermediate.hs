module Bench.Intermediate (intermediateBenchmarks) where

import Data.List (nub)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import qualified BasicKH as B
import Bench.Common
import qualified IntermediateKH as I
import qualified LTS as L

startProp :: L.Proposition
startProp = 0

goalProp :: L.Proposition
goalProp = 1

safeProp :: L.Proposition
safeProp = 2

unusedProp :: L.Proposition
unusedProp = 3

mainAction :: L.Action
mainAction = 1

safeAction :: L.Action
safeAction = 1

riskyAction :: L.Action
riskyAction = 2

rescueEnterAction :: L.Action
rescueEnterAction = 10

rescueLocateAction :: L.Action
rescueLocateAction = 11

rescueEvacuateAction :: L.Action
rescueEvacuateAction = 12

intermediateBenchmarks :: BenchMode -> [BenchCase]
intermediateBenchmarks mode =
  concat
    [ manualBenchmarks mode
    , caseStudyBenchmarks mode
    , generatedBenchmarks mode
    ]

manualBenchmarks :: BenchMode -> [BenchCase]
manualBenchmarks mode =
  [ mkICase mode "intermediate-manual-empty-plan" "manual-empty-plan"
      True "Semantic corner case: the empty plan is sufficient because every start state already satisfies the goal."
      "semantic-case" "empty-plan" (Just 0)
      manualEmptyPlanModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-vacuous-precondition" "manual-vacuous-precondition"
      True "Semantic corner case: the precondition is false everywhere, so Khm holds vacuously."
      "semantic-case" "vacuous-precondition" (Just 0)
      manualVacuousPreconditionModel (I.IP unusedProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-safe-plan" "manual-safe-plan"
      True "A two-step plan reaches the goal and its only intermediate state satisfies the constraint."
      "semantic-case" "safe-plan" (Just 2)
      manualSafePlanModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-unsafe-middle-failure" "manual-unsafe-middle-failure"
      False "The goal is reachable, but the only intermediate state violates the intermediate constraint."
      "semantic-case" "unsafe-middle" Nothing
      manualUnsafeMiddleModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-nondet-safe-success" "manual-nondet-safe-success"
      True "The first action is nondeterministic, but all intermediate successors satisfy the constraint."
      "semantic-case" "nondet-safe-success" (Just 2)
      manualNondetSafeModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-nondet-unsafe-failure" "manual-nondet-unsafe-failure"
      False "One nondeterministic intermediate successor violates the constraint, so the plan is not guaranteed."
      "semantic-case" "nondet-unsafe-failure" Nothing
      manualNondetUnsafeModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-multistart-success" "manual-multistart-success"
      True "The same safe plan works from all states satisfying the precondition."
      "semantic-case" "multistart-success" (Just 2)
      manualMultiStartSafeModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-multistart-one-bad" "manual-multistart-one-bad"
      False "One precondition state is forced through an unsafe intermediate state."
      "semantic-case" "multistart-one-bad" Nothing
      manualMultiStartOneBadModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-manual-dead-end-failure" "manual-dead-end-failure"
      False "The available path reaches a non-goal dead end, so no plan can guarantee the goal."
      "semantic-case" "dead-end-failure" Nothing
      manualDeadEndModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  ]

caseStudyBenchmarks :: BenchMode -> [BenchCase]
caseStudyBenchmarks mode =
  [ mkICase mode "intermediate-robot-safe-corridor-positive" "robot-safe-corridor"
      True "Robot corridor case study: the safe action keeps all intermediate positions safe before reaching the goal."
      "case-study" "safe-corridor" (Just 3)
      robotSafeCorridorModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-robot-unsafe-corridor-negative" "robot-unsafe-corridor"
      False "Robot corridor case study: the goal is reachable, but every route passes through an unsafe intermediate position."
      "case-study" "unsafe-corridor" Nothing
      robotUnsafeCorridorModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-robot-risky-branch-negative" "robot-risky-branch"
      False "Robot corridor case study: a risky action may either progress safely or fall into an unsafe trap."
      "case-study" "risky-branch" Nothing
      robotRiskyBranchModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-rescue-safe-route-positive" "rescue-intermediate"
      True "Autonomous rescue case study: the robot can complete the rescue while every strict intermediate state remains safe."
      "case-study" "safe-rescue-route" (Just 3)
      rescueIntermediateSafeModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)

  , mkICase mode "intermediate-rescue-smoke-route-negative" "rescue-intermediate"
      False "Autonomous rescue case study: the survivor is reachable, but every rescue route must pass through an unsafe smoke zone before the goal."
      "case-study" "smoke-route" Nothing
      rescueIntermediateSmokeModel (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  ]

generatedBenchmarks :: BenchMode -> [BenchCase]
generatedBenchmarks mode =
  concat
    [ corridorPositiveBenchmarks mode
    , corridorUnsafeMiddleBenchmarks mode
    , corridorBrokenBenchmarks mode
    , branchingDepthSafeBenchmarks mode
    , branchingDepthUnsafeBenchmarks mode
    , branchingWidthSafeBenchmarks mode
    , branchingWidthUnsafeBenchmarks mode
    , multiStartAllGoodBenchmarks mode
    , multiStartOneUnsafeBenchmarks mode
    , actionCountSafeLastBenchmarks mode
    , actionCountNoSafeBenchmarks mode
    , pathLengthSafeLastBenchmarks mode
    , pathLengthUnsafeBenchmarks mode
    , formulaDepthPositiveBenchmarks mode
    ]

corridorPositiveBenchmarks :: BenchMode -> [BenchCase]
corridorPositiveBenchmarks mode =
  [ mkICase mode ("intermediate-corridor-positive-" ++ show n) "corridor-positive"
      True "Linear corridor positive baseline: all strict intermediate states satisfy the constraint."
      "states" (show n) (Just (n - 1))
      (corridorPositiveModel n) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | n <- corridorSizes mode
  ]

corridorUnsafeMiddleBenchmarks :: BenchMode -> [BenchCase]
corridorUnsafeMiddleBenchmarks mode =
  [ mkICase mode ("intermediate-corridor-unsafe-middle-" ++ show n) "corridor-unsafe-middle"
      False "Linear corridor negative baseline: the goal is reachable but one strict intermediate state is unsafe."
      "states" (show n) Nothing
      (corridorUnsafeMiddleModel n) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | n <- corridorSizes mode
  ]

corridorBrokenBenchmarks :: BenchMode -> [BenchCase]
corridorBrokenBenchmarks mode =
  [ mkICase mode ("intermediate-corridor-broken-" ++ show n) "corridor-broken"
      False "Linear corridor negative baseline: the path stops before the goal."
      "states" (show n) Nothing
      (corridorBrokenModel n) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | n <- corridorSizes mode
  ]

branchingDepthSafeBenchmarks :: BenchMode -> [BenchCase]
branchingDepthSafeBenchmarks mode =
  [ mkICase mode ("intermediate-branching-depth-safe-d" ++ show d) "branching-depth-safe"
      True "Depth sweep with fixed branching width: all nondeterministic intermediate states are safe."
      "depth" (show d) (Just d)
      (branchingSafeModel d fixedBranchingWidth) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | d <- branchingDepths mode
  ]

branchingDepthUnsafeBenchmarks :: BenchMode -> [BenchCase]
branchingDepthUnsafeBenchmarks mode =
  [ mkICase mode ("intermediate-branching-depth-unsafe-d" ++ show d) "branching-depth-unsafe"
      False "Depth sweep with fixed branching width: one nondeterministic branch reaches an unsafe intermediate state."
      "depth" (show d) Nothing
      (branchingUnsafeModel d fixedBranchingWidth) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | d <- branchingDepths mode
  ]

branchingWidthSafeBenchmarks :: BenchMode -> [BenchCase]
branchingWidthSafeBenchmarks mode =
  [ mkICase mode ("intermediate-branching-width-safe-w" ++ show w) "branching-width-safe"
      True "Width sweep with fixed depth: all nondeterministic branches maintain the intermediate constraint."
      "width" (show w) (Just fixedBranchingDepth)
      (branchingSafeModel fixedBranchingDepth w) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | w <- branchingWidths mode
  ]

branchingWidthUnsafeBenchmarks :: BenchMode -> [BenchCase]
branchingWidthUnsafeBenchmarks mode =
  [ mkICase mode ("intermediate-branching-width-unsafe-w" ++ show w) "branching-width-unsafe"
      False "Width sweep with fixed depth: increasing width includes an unsafe branch."
      "width" (show w) Nothing
      (branchingUnsafeModel fixedBranchingDepth w) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | w <- branchingWidths mode
  ]

multiStartAllGoodBenchmarks :: BenchMode -> [BenchCase]
multiStartAllGoodBenchmarks mode =
  [ mkICase mode ("intermediate-multistart-all-good-w" ++ show w) "multi-start-all-good"
      True "Precondition sweep: the same safe plan works from every precondition state."
      "pre_states" (show w) (Just fixedMultiStartDepth)
      (multiStartAllGoodModel fixedMultiStartDepth w) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | w <- multiStartWidths mode
  ]

multiStartOneUnsafeBenchmarks :: BenchMode -> [BenchCase]
multiStartOneUnsafeBenchmarks mode =
  [ mkICase mode ("intermediate-multistart-one-unsafe-w" ++ show w) "multi-start-one-unsafe"
      False "Precondition sweep: one precondition state is forced through an unsafe intermediate state."
      "pre_states" (show w) Nothing
      (multiStartOneUnsafeModel fixedMultiStartDepth w) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | w <- multiStartWidths mode
  ]

actionCountSafeLastBenchmarks :: BenchMode -> [BenchCase]
actionCountSafeLastBenchmarks mode =
  [ mkICase mode ("intermediate-action-count-safe-last-k" ++ show k) "action-count-safe-last"
      True "Action-count sweep with fixed path length: only the last action maintains the intermediate constraint and reaches the goal."
      "actions" (show k) (Just (fixedActionPathLength - 1))
      (actionChoiceSafeLastModel fixedActionPathLength k) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | k <- actionCounts mode
  ]

actionCountNoSafeBenchmarks :: BenchMode -> [BenchCase]
actionCountNoSafeBenchmarks mode =
  [ mkICase mode ("intermediate-action-count-no-safe-k" ++ show k) "action-count-no-safe"
      False "Action-count sweep with fixed path length: every action either reaches a trap or violates the intermediate constraint."
      "actions" (show k) Nothing
      (actionChoiceNoSafeModel fixedActionPathLength k) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | k <- actionCounts mode
  ]

pathLengthSafeLastBenchmarks :: BenchMode -> [BenchCase]
pathLengthSafeLastBenchmarks mode =
  [ mkICase mode ("intermediate-path-length-safe-last-n" ++ show n) "path-length-safe-last"
      True "Path-length sweep with fixed action count: the safe action must be repeated until the goal is reached."
      "path_length" (show (n - 1)) (Just (n - 1))
      (actionChoiceSafeLastModel n fixedActionCount) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | n <- pathLengths mode
  ]

pathLengthUnsafeBenchmarks :: BenchMode -> [BenchCase]
pathLengthUnsafeBenchmarks mode =
  [ mkICase mode ("intermediate-path-length-unsafe-n" ++ show n) "path-length-unsafe"
      False "Path-length sweep with fixed action count: the available route has an unsafe strict intermediate state."
      "path_length" (show (n - 1)) Nothing
      (pathLengthUnsafeModel n fixedActionCount) (I.IP startProp) (I.IP safeProp) (I.IP goalProp)
  | n <- pathLengths mode
  ]

formulaDepthPositiveBenchmarks :: BenchMode -> [BenchCase]
formulaDepthPositiveBenchmarks mode =
  [ mkICase mode ("intermediate-formula-depth-positive-" ++ show d) "formula-depth-positive"
      True "Formula-size sweep with fixed model and fixed witness length."
      "formula_depth" (show d) (Just (fixedFormulaModelSize - 1))
      (corridorPositiveModel fixedFormulaModelSize)
      (deepConj d (I.IP startProp))
      (deepConj d (I.IP safeProp))
      (deepConj d (I.IP goalProp))
  | d <- formulaDepths mode
  ]

corridorSizes :: BenchMode -> [Int]
corridorSizes Quick = [8, 16, 32]
corridorSizes Full  = [16, 32, 64, 128]

branchingDepths :: BenchMode -> [Int]
branchingDepths Quick = [4, 6, 8]
branchingDepths Full  = [4, 6, 8, 10, 12]

branchingWidths :: BenchMode -> [Int]
branchingWidths Quick = [2, 3]
branchingWidths Full  = [2, 3, 4, 5]

multiStartWidths :: BenchMode -> [Int]
multiStartWidths Quick = [2, 4, 8]
multiStartWidths Full  = [2, 4, 8, 16]

actionCounts :: BenchMode -> [Int]
actionCounts Quick = [2, 4, 8]
actionCounts Full  = [2, 4, 8, 12, 16]

pathLengths :: BenchMode -> [Int]
pathLengths Quick = [8, 16, 24]
pathLengths Full  = [8, 16, 32, 64]

formulaDepths :: BenchMode -> [Int]
formulaDepths Quick = [32, 64, 128]
formulaDepths Full  = [64, 128, 256, 512]

fixedBranchingWidth :: Int
fixedBranchingWidth = 2

fixedBranchingDepth :: Int
fixedBranchingDepth = 8

fixedMultiStartDepth :: Int
fixedMultiStartDepth = 16

fixedActionPathLength :: Int
fixedActionPathLength = 24

fixedActionCount :: Int
fixedActionCount = 4

fixedFormulaModelSize :: Int
fixedFormulaModelSize = 64

mkICase ::
     BenchMode
  -> String
  -> String
  -> Bool
  -> String
  -> String
  -> String
  -> Maybe Int
  -> B.AbilityMap
  -> I.IForm
  -> I.IForm
  -> I.IForm
  -> BenchCase
mkICase mode name family expected purpose primaryParameter parameterValue expectedWitness model pre mid goal =
  BenchCase
    { caseName            = name
    , caseLogic           = "intermediate"
    , caseFamily          = family
    , caseMode            = mode
    , caseExpected        = Just expected
    , caseStates          = modelStateCount model
    , caseActions         = modelActionCount model
    , caseTransitions     = modelTransitionCount model
    , casePropositions    = propositionCount model pre mid goal
    , caseAgents          = Nothing
    , caseAutomata        = Nothing
    , caseAutomatonStates = Nothing
    , caseBudgetDim       = Nothing
    , caseFormulaSize     = iFormulaSize (I.Khm pre mid goal)
    , caseRun             = pure (iOutcome purpose primaryParameter parameterValue expectedWitness model pre mid goal)
    }

iOutcome :: String -> String -> String -> Maybe Int -> B.AbilityMap -> I.IForm -> I.IForm -> I.IForm -> BenchOutcome
iOutcome purpose primaryParameter parameterValue expectedWitness model pre mid goal =
  BenchOutcome
    { outcomeResult                  = result
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomePurpose                 = Just purpose
    , outcomePrimaryParameter        = Just primaryParameter
    , outcomeParameterValue          = Just parameterValue
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable model preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable model preStates goalStates
    , outcomeExpectedWitnessSize     = expectedWitness
    , outcomeWitnessSizePassed       = witnessSizePassed expectedWitness witnessSize
    }
  where
    preStates =
      I.truthSetI model pre

    midStates =
      I.truthSetI model mid

    goalStates =
      I.truthSetI model goal

    witness =
      I.findWitnessKhm model pre mid goal

    witnessFound =
      case witness of
        Nothing -> False
        Just _  -> True

    witnessSize =
      fmap length witness

    result =
      case witness of
        Nothing ->
          False
        Just plan ->
          iWitnessSound model preStates midStates goalStates plan

witnessSizePassed :: Maybe Int -> Maybe Int -> Maybe Bool
witnessSizePassed Nothing _ =
  Nothing
witnessSizePassed (Just expected) actual =
  Just (actual == Just expected)

iWitnessSound :: B.AbilityMap -> [L.State] -> [L.State] -> [L.State] -> L.Plan -> Bool
iWitnessSound model preStates midStates goalStates plan =
  all checkStart preStates
  where
    rs =
      B.transitions model

    checkStart s =
      L.stronglyExecutableAt rs s plan
      && all (`elem` goalStates) (L.executePlan rs s plan)
      && all (all (`elem` midStates)) (strictIntermediateImages rs s plan)

strictIntermediateImages :: L.Relations -> L.State -> L.Plan -> [[L.State]]
strictIntermediateImages rs s plan =
  [ L.executePlan rs s prefix
  | k <- [1 .. length plan - 1]
  , let prefix = take k plan
  ]

ordinaryReachable :: B.AbilityMap -> [L.State] -> [L.State] -> Maybe Bool
ordinaryReachable _ [] _ =
  Nothing
ordinaryReachable _ _ [] =
  Nothing
ordinaryReachable model preStates goalStates =
  Just (any reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates model s)

ordinaryAllPreReachable :: B.AbilityMap -> [L.State] -> [L.State] -> Maybe Bool
ordinaryAllPreReachable _ [] _ =
  Nothing
ordinaryAllPreReachable _ _ [] =
  Nothing
ordinaryAllPreReachable model preStates goalStates =
  Just (all reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates model s)

reachableStates :: B.AbilityMap -> L.State -> [L.State]
reachableStates model start =
  go [] [start]
  where
    edges =
      nub (concatMap snd (B.transitions model))

    successors s =
      [v | (u, v) <- edges, u == s]

    go visited [] =
      visited

    go visited (x:queue)
      | x `elem` visited =
          go visited queue
      | otherwise =
          go (x:visited) (queue ++ successors x)

manualEmptyPlanModel :: B.AbilityMap
manualEmptyPlanModel =
  mkModel
    [0, 1]
    []
    [ (0, [startProp, goalProp])
    , (1, [])
    ]

manualVacuousPreconditionModel :: B.AbilityMap
manualVacuousPreconditionModel =
  mkModel
    [0, 1]
    []
    [ (0, [])
    , (1, [goalProp])
    ]

manualSafePlanModel :: B.AbilityMap
manualSafePlanModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1)])
    , (2, [(1, 2)])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [goalProp])
    ]

manualUnsafeMiddleModel :: B.AbilityMap
manualUnsafeMiddleModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1)])
    , (2, [(1, 2)])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [goalProp])
    ]

manualNondetSafeModel :: B.AbilityMap
manualNondetSafeModel =
  mkModel
    [0, 1, 2, 3]
    [ (1, [(0, 1), (0, 2)])
    , (2, [(1, 3), (2, 3)])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [safeProp])
    , (3, [goalProp])
    ]

manualNondetUnsafeModel :: B.AbilityMap
manualNondetUnsafeModel =
  mkModel
    [0, 1, 2, 3]
    [ (1, [(0, 1), (0, 2)])
    , (2, [(1, 3), (2, 3)])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [])
    , (3, [goalProp])
    ]

manualMultiStartSafeModel :: B.AbilityMap
manualMultiStartSafeModel =
  mkModel
    [0, 1, 2, 3]
    [ (1, [(0, 2), (1, 2)])
    , (2, [(2, 3)])
    ]
    [ (0, [startProp])
    , (1, [startProp])
    , (2, [safeProp])
    , (3, [goalProp])
    ]

manualMultiStartOneBadModel :: B.AbilityMap
manualMultiStartOneBadModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (1, [(0, 2), (1, 4)])
    , (2, [(2, 3), (4, 3)])
    ]
    [ (0, [startProp])
    , (1, [startProp])
    , (2, [safeProp])
    , (3, [goalProp])
    , (4, [])
    ]

manualDeadEndModel :: B.AbilityMap
manualDeadEndModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1)])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [goalProp])
    ]

robotSafeCorridorModel :: B.AbilityMap
robotSafeCorridorModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (safeAction, [(0, 1), (1, 2), (2, 3), (3, 3), (4, 4)])
    , (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [safeProp])
    , (3, [goalProp])
    , (4, [])
    ]

robotUnsafeCorridorModel :: B.AbilityMap
robotUnsafeCorridorModel =
  mkModel
    [0, 1, 2, 3]
    [ (safeAction, [(0, 1), (1, 2), (2, 3)]) ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [])
    , (3, [goalProp])
    ]

robotRiskyBranchModel :: B.AbilityMap
robotRiskyBranchModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)]) ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [safeProp])
    , (3, [goalProp])
    , (4, [])
    ]


rescueIntermediateSafeModel :: B.AbilityMap
rescueIntermediateSafeModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (rescueEnterAction,
        [ (0, 1)
        , (1, 1)
        , (2, 2)
        , (3, 3)
        , (4, 4)
        ])
    , (rescueLocateAction,
        [ (0, 0)
        , (1, 2)
        , (2, 2)
        , (3, 3)
        , (4, 4)
        ])
    , (rescueEvacuateAction,
        [ (0, 0)
        , (1, 1)
        , (2, 3)
        , (3, 3)
        , (4, 4)
        ])
    ]
    [ (0, [startProp])
    , (1, [safeProp])
    , (2, [safeProp])
    , (3, [goalProp])
    , (4, [])
    ]

rescueIntermediateSmokeModel :: B.AbilityMap
rescueIntermediateSmokeModel =
  mkModel
    [0, 1, 2, 3]
    [ (rescueEnterAction,
        [ (0, 1)
        ])
    , (rescueLocateAction,
        [ (1, 2)
        ])
    , (rescueEvacuateAction,
        [ (2, 3)
        ])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [safeProp])
    , (3, [goalProp])
    ]

corridorPositiveModel :: Int -> B.AbilityMap
corridorPositiveModel n0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    sts =
      [0 .. n - 1]

    rels =
      [(mainAction, [(i, i + 1) | i <- [0 .. n - 2]])]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

corridorUnsafeMiddleModel :: Int -> B.AbilityMap
corridorUnsafeMiddleModel n0 =
  mkModel sts rels vals
  where
    n =
      max 4 n0

    bad =
      n `div` 2

    sts =
      [0 .. n - 1]

    rels =
      [(mainAction, [(i, i + 1) | i <- [0 .. n - 2]])]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1 && s /= bad, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

corridorBrokenModel :: Int -> B.AbilityMap
corridorBrokenModel n0 =
  mkModel sts rels vals
  where
    n =
      max 4 n0

    dead =
      n - 2

    sts =
      [0 .. n - 1]

    rels =
      [(mainAction, [(i, i + 1) | i <- [0 .. dead - 1]] ++ [(dead, dead)])]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

branchingSafeModel :: Int -> Int -> B.AbilityMap
branchingSafeModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 1 depth0

    width =
      max 1 width0

    totalStates =
      1 + depth * width

    sts =
      [0 .. totalStates - 1]

    node level i =
      1 + (level - 1) * width + i

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    intermediateStates =
      [node level i | level <- [1 .. depth - 1], i <- [0 .. width - 1]]

    firstLayerEdges =
      [(0, node 1 j) | j <- [0 .. width - 1]]

    innerEdges =
      [ (node level i, node (level + 1) j)
      | level <- [1 .. depth - 1]
      , i <- [0 .. width - 1]
      , j <- [0 .. width - 1]
      ]

    rels =
      [(mainAction, firstLayerEdges ++ innerEdges)]

    vals =
      [ (s, props [(s == 0, startProp), (s `elem` intermediateStates, safeProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

branchingUnsafeModel :: Int -> Int -> B.AbilityMap
branchingUnsafeModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 2 depth0

    width =
      max 2 width0

    totalStates =
      1 + depth * width

    sts =
      [0 .. totalStates - 1]

    node level i =
      1 + (level - 1) * width + i

    unsafe =
      node 1 (width - 1)

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    intermediateStates =
      [node level i | level <- [1 .. depth - 1], i <- [0 .. width - 1], node level i /= unsafe]

    firstLayerEdges =
      [(0, node 1 j) | j <- [0 .. width - 1]]

    innerEdges =
      [ (node level i, node (level + 1) j)
      | level <- [1 .. depth - 1]
      , i <- [0 .. width - 1]
      , j <- [0 .. width - 1]
      ]

    rels =
      [(mainAction, firstLayerEdges ++ innerEdges)]

    vals =
      [ (s, props [(s == 0, startProp), (s `elem` intermediateStates, safeProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

multiStartAllGoodModel :: Int -> Int -> B.AbilityMap
multiStartAllGoodModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 1 depth0

    width =
      max 1 width0

    totalStates =
      (depth + 1) * width

    sts =
      [0 .. totalStates - 1]

    node level i =
      level * width + i

    startStates =
      [node 0 i | i <- [0 .. width - 1]]

    safeStates =
      [node level i | level <- [1 .. depth - 1], i <- [0 .. width - 1]]

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    edges =
      [ (node level i, node (level + 1) i)
      | level <- [0 .. depth - 1]
      , i <- [0 .. width - 1]
      ]

    rels =
      [(mainAction, edges)]

    vals =
      [ (s, props [(s `elem` startStates, startProp), (s `elem` safeStates, safeProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

multiStartOneUnsafeModel :: Int -> Int -> B.AbilityMap
multiStartOneUnsafeModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 2 depth0

    width =
      max 2 width0

    totalStates =
      (depth + 1) * width

    sts =
      [0 .. totalStates - 1]

    node level i =
      level * width + i

    badLane =
      width - 1

    startStates =
      [node 0 i | i <- [0 .. width - 1]]

    safeStates =
      [node level i | level <- [1 .. depth - 1], i <- [0 .. width - 1], not (level == 1 && i == badLane)]

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    edges =
      [ (node level i, node (level + 1) i)
      | level <- [0 .. depth - 1]
      , i <- [0 .. width - 1]
      ]

    rels =
      [(mainAction, edges)]

    vals =
      [ (s, props [(s `elem` startStates, startProp), (s `elem` safeStates, safeProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

actionChoiceSafeLastModel :: Int -> Int -> B.AbilityMap
actionChoiceSafeLastModel n0 k0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    k =
      max 2 k0

    trap =
      n

    sts =
      [0 .. trap]

    good =
      k

    bads =
      [1 .. k - 1]

    goodEdges =
      [(i, i + 1) | i <- [0 .. n - 2]]
      ++ [(n - 1, n - 1), (trap, trap)]

    badEdges =
      [(s, trap) | s <- [0 .. n - 1]]
      ++ [(trap, trap)]

    rels =
      [(a, badEdges) | a <- bads]
      ++ [(good, goodEdges)]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

actionChoiceNoSafeModel :: Int -> Int -> B.AbilityMap
actionChoiceNoSafeModel n0 k0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    k =
      max 1 k0

    trap =
      n

    sts =
      [0 .. trap]

    badEdges =
      [(s, trap) | s <- [0 .. n - 1]]
      ++ [(trap, trap)]

    rels =
      [(a, badEdges) | a <- [1 .. k]]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

pathLengthUnsafeModel :: Int -> Int -> B.AbilityMap
pathLengthUnsafeModel n0 k0 =
  mkModel sts rels vals
  where
    n =
      max 4 n0

    k =
      max 1 k0

    bad =
      n `div` 2

    sts =
      [0 .. n - 1]

    edges =
      [(i, i + 1) | i <- [0 .. n - 2]]

    rels =
      [(a, edges) | a <- [1 .. k]]

    vals =
      [ (s, props [(s == 0, startProp), (s > 0 && s < n - 1 && s /= bad, safeProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

deepConj :: Int -> I.IForm -> I.IForm
deepConj n f =
  foldr I.IConj f (replicate (max 0 n) I.IT)

mkModel :: [L.State] -> L.Relations -> L.Valuation -> B.AbilityMap
mkModel [] _ _ =
  error "intermediate benchmark model must contain at least one state"
mkModel (s:ss) rels vals =
  B.LTS
    { B.states = s :| ss
    , B.transitions = rels
    , B.valuation = vals
    }

props :: [(Bool, L.Proposition)] -> [L.Proposition]
props xs =
  [p | (ok, p) <- xs, ok]

modelStateCount :: B.AbilityMap -> Int
modelStateCount model =
  length (NE.toList (B.states model))

modelActionCount :: B.AbilityMap -> Int
modelActionCount model =
  length (L.actionsOf (B.transitions model))

modelTransitionCount :: B.AbilityMap -> Int
modelTransitionCount model =
  sum [length rel | (_, rel) <- B.transitions model]

propositionCount :: B.AbilityMap -> I.IForm -> I.IForm -> I.IForm -> Int
propositionCount model pre mid goal =
  length . nub $
    concatMap snd (B.valuation model)
    ++ iFormPropositions pre
    ++ iFormPropositions mid
    ++ iFormPropositions goal

iFormulaSize :: I.IForm -> Int
iFormulaSize I.IT =
  1
iFormulaSize (I.IP _) =
  1
iFormulaSize (I.INeg f) =
  1 + iFormulaSize f
iFormulaSize (I.IConj f g) =
  1 + iFormulaSize f + iFormulaSize g
iFormulaSize (I.Khm f g h) =
  1 + iFormulaSize f + iFormulaSize g + iFormulaSize h

iFormPropositions :: I.IForm -> [L.Proposition]
iFormPropositions I.IT =
  []
iFormPropositions (I.IP p) =
  [p]
iFormPropositions (I.INeg f) =
  iFormPropositions f
iFormPropositions (I.IConj f g) =
  iFormPropositions f ++ iFormPropositions g
iFormPropositions (I.Khm f g h) =
  iFormPropositions f ++ iFormPropositions g ++ iFormPropositions h