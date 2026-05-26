module Bench.Basic (basicBenchmarks) where

import Data.List (nub)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import qualified BasicKH as B
import Bench.Common
import qualified LTS as L

startProp :: L.Proposition
startProp = 0

goalProp :: L.Proposition
goalProp = 1

unusedProp :: L.Proposition
unusedProp = 2

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

rescueRiskyAction :: L.Action
rescueRiskyAction = 13

basicBenchmarks :: BenchMode -> [BenchCase]
basicBenchmarks mode =
  concat
    [ manualBenchmarks mode
    , caseStudyBenchmarks mode
    , generatedBenchmarks mode
    ]

manualBenchmarks :: BenchMode -> [BenchCase]
manualBenchmarks mode =
  [ mkBasicCase mode "basic-manual-empty-plan" "manual-empty-plan"
      True "Semantic corner case: the empty plan is sufficient because every start state already satisfies the goal."
      "semantic-case" "empty-plan" (Just 0)
      manualEmptyPlanModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-vacuous-precondition" "manual-vacuous-precondition"
      True "Semantic corner case: the precondition is false everywhere, so Kh holds vacuously."
      "semantic-case" "vacuous-precondition" (Just 0)
      manualVacuousPreconditionModel (B.P unusedProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-reliable-plan" "manual-reliable-plan"
      True "A deterministic two-step plan witnesses Kh(start,goal)."
      "semantic-case" "reliable-plan" (Just 2)
      manualReliablePlanModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-nondet-success" "manual-nondet-success"
      True "The first action is nondeterministic, but every possible successor satisfies the goal."
      "semantic-case" "nondet-success" (Just 1)
      manualNondetSuccessModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-multistart-success" "manual-multistart-success"
      True "The same one-step plan works from all states satisfying the precondition."
      "semantic-case" "multistart-success" (Just 1)
      manualMultiStartModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-trap-failure" "manual-trap-failure"
      False "Reachability is not enough: the action may also lead to a non-goal trap."
      "semantic-case" "trap-failure" Nothing
      manualTrapFailureModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-manual-dead-end-failure" "manual-dead-end-failure"
      False "The available action reaches a dead non-goal state, so no plan guarantees the goal."
      "semantic-case" "dead-end-failure" Nothing
      manualDeadEndFailureModel (B.P startProp) (B.P goalProp)
  ]

caseStudyBenchmarks :: BenchMode -> [BenchCase]
caseStudyBenchmarks mode =
  [ mkBasicCase mode "basic-robot-safe-plan-positive" "robot-corridor-safe-plan"
      True "Robot corridor case study: a safe action guarantees progress to the goal despite the presence of risky behaviour."
      "case-study" "safe-plan" (Just 3)
      robotSafePlanModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-robot-risky-only-negative" "robot-corridor-risky-only"
      False "Robot corridor case study: the goal is reachable, but every risky move can also fall into a trap."
      "case-study" "risky-only" Nothing
      robotRiskyOnlyModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-robot-multistart-positive" "robot-corridor-multistart"
      True "Robot corridor case study: the same safe plan works from multiple possible starting states."
      "case-study" "multi-start" (Just 2)
      robotMultiStartModel (B.P startProp) (B.P goalProp)
      
  , mkBasicCase mode "basic-rescue-safe-route-positive" "rescue-basic"
      True "Autonomous rescue case study: the robot has a reliable plan to enter the building, locate the survivor, and complete the evacuation."
      "case-study" "safe-rescue-route" (Just 3)
      rescueBasicSafeModel (B.P startProp) (B.P goalProp)

  , mkBasicCase mode "basic-rescue-risky-branch-negative" "rescue-basic"
      False "Autonomous rescue case study: the survivor is reachable, but the only available risky move can also lead to a smoke or collapse trap."
      "case-study" "risky-rescue-branch" Nothing
      rescueBasicRiskyModel (B.P startProp) (B.P goalProp)
  ]

generatedBenchmarks :: BenchMode -> [BenchCase]
generatedBenchmarks mode =
  concat
    [ linePositiveBenchmarks mode
    , lineBrokenNegativeBenchmarks mode
    , branchingDepthSafeBenchmarks mode
    , branchingDepthTrapBenchmarks mode
    , branchingWidthSafeBenchmarks mode
    , branchingWidthTrapBenchmarks mode
    , multiStartAllGoodBenchmarks mode
    , multiStartOneBadBenchmarks mode
    , actionCountGoodLastBenchmarks mode
    , actionCountNoGoodBenchmarks mode
    , pathLengthGoodLastBenchmarks mode
    , pathLengthNoGoodBenchmarks mode
    , trapReachableNegativeBenchmarks mode
    , formulaDepthPositiveBenchmarks mode
    ]

linePositiveBenchmarks :: BenchMode -> [BenchCase]
linePositiveBenchmarks mode =
  [ mkBasicCase mode ("basic-line-positive-" ++ show n) "line-positive"
      True "Linear positive baseline: increasing states also increases the required witness length."
      "states" (show n) (Just (n - 1))
      (linePositiveModel n) (B.P startProp) (B.P goalProp)
  | n <- lineSizes mode
  ]

lineBrokenNegativeBenchmarks :: BenchMode -> [BenchCase]
lineBrokenNegativeBenchmarks mode =
  [ mkBasicCase mode ("basic-line-broken-negative-" ++ show n) "line-broken-negative"
      False "Linear negative baseline: the path stops before the goal, so the goal is not guaranteed."
      "states" (show n) Nothing
      (lineBrokenNegativeModel n) (B.P startProp) (B.P goalProp)
  | n <- lineSizes mode
  ]

branchingDepthSafeBenchmarks :: BenchMode -> [BenchCase]
branchingDepthSafeBenchmarks mode =
  [ mkBasicCase mode ("basic-branching-depth-safe-d" ++ show d) "branching-depth-safe-positive"
      True "Depth sweep with fixed branching width: all nondeterministic branches eventually reach the goal."
      "depth" (show d) (Just d)
      (branchingSafeModel d fixedBranchingWidth) (B.P startProp) (B.P goalProp)
  | d <- branchingDepths mode
  ]

branchingDepthTrapBenchmarks :: BenchMode -> [BenchCase]
branchingDepthTrapBenchmarks mode =
  [ mkBasicCase mode ("basic-branching-depth-trap-d" ++ show d) "branching-depth-trap-negative"
      False "Depth sweep with fixed branching width: one branch can enter a non-goal trap."
      "depth" (show d) Nothing
      (branchingTrapModel d fixedBranchingWidth) (B.P startProp) (B.P goalProp)
  | d <- branchingDepths mode
  ]

branchingWidthSafeBenchmarks :: BenchMode -> [BenchCase]
branchingWidthSafeBenchmarks mode =
  [ mkBasicCase mode ("basic-branching-width-safe-w" ++ show w) "branching-width-safe-positive"
      True "Width sweep with fixed depth: all nondeterministic branches remain safe."
      "width" (show w) (Just fixedBranchingDepth)
      (branchingSafeModel fixedBranchingDepth w) (B.P startProp) (B.P goalProp)
  | w <- branchingWidths mode
  ]

branchingWidthTrapBenchmarks :: BenchMode -> [BenchCase]
branchingWidthTrapBenchmarks mode =
  [ mkBasicCase mode ("basic-branching-width-trap-w" ++ show w) "branching-width-trap-negative"
      False "Width sweep with fixed depth: nondeterminism includes a bad trap branch."
      "width" (show w) Nothing
      (branchingTrapModel fixedBranchingDepth w) (B.P startProp) (B.P goalProp)
  | w <- branchingWidths mode
  ]

multiStartAllGoodBenchmarks :: BenchMode -> [BenchCase]
multiStartAllGoodBenchmarks mode =
  [ mkBasicCase mode ("basic-multistart-all-good-w" ++ show w) "multi-start-all-good"
      True "Precondition sweep: the same plan succeeds from every precondition state."
      "pre_states" (show w) (Just fixedMultiStartDepth)
      (multiStartAllGoodModel fixedMultiStartDepth w) (B.P startProp) (B.P goalProp)
  | w <- multiStartWidths mode
  ]

multiStartOneBadBenchmarks :: BenchMode -> [BenchCase]
multiStartOneBadBenchmarks mode =
  [ mkBasicCase mode ("basic-multistart-one-bad-w" ++ show w) "multi-start-one-bad"
      False "Precondition sweep: one precondition state cannot be guaranteed to reach the goal."
      "pre_states" (show w) Nothing
      (multiStartOneBadModel fixedMultiStartDepth w) (B.P startProp) (B.P goalProp)
  | w <- multiStartWidths mode
  ]

actionCountGoodLastBenchmarks :: BenchMode -> [BenchCase]
actionCountGoodLastBenchmarks mode =
  [ mkBasicCase mode ("basic-action-count-good-last-k" ++ show k) "action-count-good-last"
      True "Action-count sweep with fixed path length: only the last action is useful."
      "actions" (show k) (Just (fixedActionPathLength - 1))
      (actionChoiceGoodLastModel fixedActionPathLength k) (B.P startProp) (B.P goalProp)
  | k <- actionCounts mode
  ]

actionCountNoGoodBenchmarks :: BenchMode -> [BenchCase]
actionCountNoGoodBenchmarks mode =
  [ mkBasicCase mode ("basic-action-count-no-good-k" ++ show k) "action-count-no-good"
      False "Action-count sweep with fixed path length: every available action leads to a trap."
      "actions" (show k) Nothing
      (actionChoiceNoGoodModel fixedActionPathLength k) (B.P startProp) (B.P goalProp)
  | k <- actionCounts mode
  ]

pathLengthGoodLastBenchmarks :: BenchMode -> [BenchCase]
pathLengthGoodLastBenchmarks mode =
  [ mkBasicCase mode ("basic-path-length-good-last-n" ++ show n) "path-length-good-last"
      True "Path-length sweep with fixed action count: the good action must be repeated until the goal is reached."
      "path_length" (show (n - 1)) (Just (n - 1))
      (actionChoiceGoodLastModel n fixedActionCount) (B.P startProp) (B.P goalProp)
  | n <- pathLengths mode
  ]

pathLengthNoGoodBenchmarks :: BenchMode -> [BenchCase]
pathLengthNoGoodBenchmarks mode =
  [ mkBasicCase mode ("basic-path-length-no-good-n" ++ show n) "path-length-no-good"
      False "Path-length sweep with fixed action count: no action can make progress to the goal."
      "path_length" (show (n - 1)) Nothing
      (actionChoiceNoGoodModel n fixedActionCount) (B.P startProp) (B.P goalProp)
  | n <- pathLengths mode
  ]

trapReachableNegativeBenchmarks :: BenchMode -> [BenchCase]
trapReachableNegativeBenchmarks mode =
  [ mkBasicCase mode ("basic-trap-reachable-negative-" ++ show n) "trap-reachable-negative"
      False "Reachability separator: the goal is reachable along some path, but the same action can also lead to a trap."
      "states" (show n) Nothing
      (trapReachableNegativeModel n) (B.P startProp) (B.P goalProp)
  | n <- trapSizes mode
  ]

formulaDepthPositiveBenchmarks :: BenchMode -> [BenchCase]
formulaDepthPositiveBenchmarks mode =
  [ mkBasicCase mode ("basic-formula-depth-positive-" ++ show d) "formula-depth-positive"
      True "Formula-size sweep with fixed model size and fixed witness length."
      "formula_depth" (show d) (Just (fixedFormulaModelSize - 1))
      (linePositiveModel fixedFormulaModelSize)
      (deepConj d (B.P startProp))
      (deepConj d (B.P goalProp))
  | d <- formulaDepths mode
  ]

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

lineSizes :: BenchMode -> [Int]
lineSizes Quick = [16, 32, 64]
lineSizes Full  = [32, 64, 128, 256]

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

trapSizes :: BenchMode -> [Int]
trapSizes Quick = [32, 64]
trapSizes Full  = [64, 128, 256]

formulaDepths :: BenchMode -> [Int]
formulaDepths Quick = [32, 64, 128]
formulaDepths Full  = [64, 128, 256, 512, 1024]

mkBasicCase ::
     BenchMode
  -> String
  -> String
  -> Bool
  -> String
  -> String
  -> String
  -> Maybe Int
  -> B.AbilityMap
  -> B.Form
  -> B.Form
  -> BenchCase
mkBasicCase mode name family expected purpose primaryParameter parameterValue expectedWitness model pre goal =
  BenchCase
    { caseName            = name
    , caseLogic           = "basic"
    , caseFamily          = family
    , caseMode            = mode
    , caseExpected        = Just expected
    , caseStates          = modelStateCount model
    , caseActions         = modelActionCount model
    , caseTransitions     = modelTransitionCount model
    , casePropositions    = propositionCount model pre goal
    , caseAgents          = Nothing
    , caseAutomata        = Nothing
    , caseAutomatonStates = Nothing
    , caseBudgetDim       = Nothing
    , caseFormulaSize     = khFormulaSize pre goal
    , caseRun             = pure (khOutcome purpose primaryParameter parameterValue expectedWitness model pre goal)
    }

khOutcome :: String -> String -> String -> Maybe Int -> B.AbilityMap -> B.Form -> B.Form -> BenchOutcome
khOutcome purpose primaryParameter parameterValue expectedWitness model pre goal =
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
      B.truthSet model pre

    goalStates =
      B.truthSet model goal

    witness =
      B.findWitness model pre goal

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
          witnessSound model pre goal plan

witnessSizePassed :: Maybe Int -> Maybe Int -> Maybe Bool
witnessSizePassed Nothing _ =
  Nothing
witnessSizePassed (Just expected) actual =
  Just (actual == Just expected)

witnessSound :: B.AbilityMap -> B.Form -> B.Form -> L.Plan -> Bool
witnessSound model pre goal plan =
  all checkState preStates
  where
    preStates =
      B.truthSet model pre

    goalStates =
      B.truthSet model goal

    rs =
      B.transitions model

    checkState s =
      L.stronglyExecutableAt rs s plan
      && all (`elem` goalStates) (L.executePlan rs s plan)

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

manualReliablePlanModel :: B.AbilityMap
manualReliablePlanModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1)])
    , (2, [(1, 2)])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [goalProp])
    ]

manualNondetSuccessModel :: B.AbilityMap
manualNondetSuccessModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1), (0, 2), (1, 1), (2, 2)])
    ]
    [ (0, [startProp])
    , (1, [goalProp])
    , (2, [goalProp])
    ]

manualMultiStartModel :: B.AbilityMap
manualMultiStartModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 2), (1, 2), (2, 2)])
    ]
    [ (0, [startProp])
    , (1, [startProp])
    , (2, [goalProp])
    ]

manualTrapFailureModel :: B.AbilityMap
manualTrapFailureModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1), (0, 2), (1, 1), (2, 2)])
    ]
    [ (0, [startProp])
    , (1, [goalProp])
    , (2, [])
    ]

manualDeadEndFailureModel :: B.AbilityMap
manualDeadEndFailureModel =
  mkModel
    [0, 1, 2]
    [ (1, [(0, 1)])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [goalProp])
    ]

robotSafePlanModel :: B.AbilityMap
robotSafePlanModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (safeAction,  [(0, 1), (1, 2), (2, 3), (3, 3), (4, 4)])
    , (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [])
    , (3, [goalProp])
    , (4, [])
    ]

robotRiskyOnlyModel :: B.AbilityMap
robotRiskyOnlyModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [])
    , (3, [goalProp])
    , (4, [])
    ]

robotMultiStartModel :: B.AbilityMap
robotMultiStartModel =
  mkModel
    [0, 1, 2, 3]
    [ (safeAction, [(0, 2), (1, 2), (2, 3), (3, 3)])
    ]
    [ (0, [startProp])
    , (1, [startProp])
    , (2, [])
    , (3, [goalProp])
    ]

rescueBasicSafeModel :: B.AbilityMap
rescueBasicSafeModel =
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
    , (rescueRiskyAction,
        [ (0, 4)
        , (1, 4)
        , (2, 4)
        , (3, 3)
        , (4, 4)
        ])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [])
    , (3, [goalProp])
    , (4, [])
    ]

rescueBasicRiskyModel :: B.AbilityMap
rescueBasicRiskyModel =
  mkModel
    [0, 1, 2, 3, 4]
    [ (rescueRiskyAction,
        [ (0, 1)
        , (0, 4)
        , (1, 2)
        , (1, 4)
        , (2, 3)
        , (2, 4)
        , (3, 3)
        , (4, 4)
        ])
    ]
    [ (0, [startProp])
    , (1, [])
    , (2, [])
    , (3, [goalProp])
    , (4, [])
    ]

linePositiveModel :: Int -> B.AbilityMap
linePositiveModel n0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    sts =
      [0 .. n - 1]

    rels =
      [ (mainAction, [(i, i + 1) | i <- [0 .. n - 2]]) ]

    vals =
      [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

lineBrokenNegativeModel :: Int -> B.AbilityMap
lineBrokenNegativeModel n0 =
  mkModel sts rels vals
  where
    n =
      max 3 n0

    dead =
      n - 2

    goal =
      n - 1

    sts =
      [0 .. n - 1]

    rels =
      [ (mainAction, [(i, i + 1) | i <- [0 .. dead - 1]] ++ [(dead, dead)]) ]

    vals =
      [ (s, props [(s == 0, startProp), (s == goal, goalProp)])
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

    firstLayerEdges =
      [(0, node 1 j) | j <- [0 .. width - 1]]

    innerEdges =
      [ (node level i, node (level + 1) j)
      | level <- [1 .. depth - 1]
      , i <- [0 .. width - 1]
      , j <- [0 .. width - 1]
      ]

    rels =
      [ (mainAction, firstLayerEdges ++ innerEdges) ]

    vals =
      [ (s, props [(s == 0, startProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

branchingTrapModel :: Int -> Int -> B.AbilityMap
branchingTrapModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 1 depth0

    width =
      max 1 width0

    totalSafeStates =
      1 + depth * width

    trap =
      totalSafeStates

    sts =
      [0 .. trap]

    node level i =
      1 + (level - 1) * width + i

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    firstLayerEdges =
      [(0, node 1 j) | j <- [0 .. width - 1]] ++ [(0, trap)]

    innerEdges =
      [ (node level i, node (level + 1) j)
      | level <- [1 .. depth - 1]
      , i <- [0 .. width - 1]
      , j <- [0 .. width - 1]
      ]

    rels =
      [ (mainAction, firstLayerEdges ++ innerEdges ++ [(trap, trap)]) ]

    vals =
      [ (s, props [(s == 0, startProp), (s `elem` goalStates, goalProp)])
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

    goalStates =
      [node depth i | i <- [0 .. width - 1]]

    edges =
      [ (node level i, node (level + 1) i)
      | level <- [0 .. depth - 1]
      , i <- [0 .. width - 1]
      ]

    rels =
      [ (mainAction, edges) ]

    vals =
      [ (s, props [(s `elem` startStates, startProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

multiStartOneBadModel :: Int -> Int -> B.AbilityMap
multiStartOneBadModel depth0 width0 =
  mkModel sts rels vals
  where
    depth =
      max 1 depth0

    width =
      max 2 width0

    baseStates =
      (depth + 1) * width

    trap =
      baseStates

    sts =
      [0 .. trap]

    node level i =
      level * width + i

    badLane =
      width - 1

    startStates =
      [node 0 i | i <- [0 .. width - 1]]

    goalStates =
      [node depth i | i <- [0 .. width - 2]]

    goodEdges =
      [ (node level i, node (level + 1) i)
      | level <- [0 .. depth - 1]
      , i <- [0 .. width - 2]
      ]

    badEdges =
      [(node 0 badLane, trap), (trap, trap)]

    rels =
      [ (mainAction, goodEdges ++ badEdges) ]

    vals =
      [ (s, props [(s `elem` startStates, startProp), (s `elem` goalStates, goalProp)])
      | s <- sts
      ]

actionChoiceGoodLastModel :: Int -> Int -> B.AbilityMap
actionChoiceGoodLastModel n0 k0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    k =
      max 2 k0

    trap =
      n

    sts =
      [0 .. n]

    goodAction =
      k

    badActions =
      [1 .. k - 1]

    goodEdges =
      [(i, i + 1) | i <- [0 .. n - 2]]
      ++ [(n - 1, n - 1), (trap, trap)]

    badEdges =
      [(s, trap) | s <- [0 .. n - 1]]
      ++ [(trap, trap)]

    rels =
      [(a, badEdges) | a <- badActions]
      ++ [(goodAction, goodEdges)]

    vals =
      [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

actionChoiceNoGoodModel :: Int -> Int -> B.AbilityMap
actionChoiceNoGoodModel n0 k0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    k =
      max 1 k0

    trap =
      n

    sts =
      [0 .. n]

    badEdges =
      [(s, trap) | s <- [0 .. n - 1]]
      ++ [(trap, trap)]

    rels =
      [(a, badEdges) | a <- [1 .. k]]

    vals =
      [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

trapReachableNegativeModel :: Int -> B.AbilityMap
trapReachableNegativeModel n0 =
  mkModel sts rels vals
  where
    n =
      max 2 n0

    trap =
      n

    sts =
      [0 .. n]

    progressEdges =
      [(i, i + 1) | i <- [0 .. n - 2]]

    trapEdges =
      [(i, trap) | i <- [0 .. n - 2]]
      ++ [(n - 1, n - 1), (trap, trap)]

    rels =
      [ (mainAction, nub (progressEdges ++ trapEdges)) ]

    vals =
      [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
      | s <- sts
      ]

deepConj :: Int -> B.Form -> B.Form
deepConj n f =
  foldr B.Conj f (replicate (max 0 n) B.T)

mkModel :: [L.State] -> L.Relations -> L.Valuation -> B.AbilityMap
mkModel [] _ _ =
  error "benchmark model must contain at least one state"
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

propositionCount :: B.AbilityMap -> B.Form -> B.Form -> Int
propositionCount model pre goal =
  length . nub $
    concatMap snd (B.valuation model)
    ++ formPropositions pre
    ++ formPropositions goal

khFormulaSize :: B.Form -> B.Form -> Int
khFormulaSize pre goal =
  1 + formSize pre + formSize goal

formSize :: B.Form -> Int
formSize B.T =
  1
formSize (B.P _) =
  1
formSize (B.Neg f) =
  1 + formSize f
formSize (B.Conj f g) =
  1 + formSize f + formSize g
formSize (B.KH f g) =
  1 + formSize f + formSize g

formPropositions :: B.Form -> [L.Proposition]
formPropositions B.T =
  []
formPropositions (B.P p) =
  [p]
formPropositions (B.Neg f) =
  formPropositions f
formPropositions (B.Conj f g) =
  formPropositions f ++ formPropositions g
formPropositions (B.KH f g) =
  formPropositions f ++ formPropositions g