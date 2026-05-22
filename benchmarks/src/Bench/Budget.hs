module Bench.Budget (budgetBenchmarks) where

import Data.List (nub)

import Automata
import qualified BudgetRegKH as B
import Bench.Common
import qualified RegKH as R

startProp :: Int
startProp = 0

goalProp :: Int
goalProp = 1

unusedProp :: Int
unusedProp = 2

cheapAction :: Int
cheapAction = 1

expensiveAction :: Int
expensiveAction = 2

agentOne :: Int
agentOne = 1

budgetBenchmarks :: BenchMode -> [BenchCase]
budgetBenchmarks mode =
  concat
    [ manualBenchmarks mode
    , caseStudyBenchmarks mode
    , generatedBenchmarks mode
    ]

manualBenchmarks :: BenchMode -> [BenchCase]
manualBenchmarks mode =
  [ mkBudgetCase mode "budget-manual-empty-plan" "manual-empty-plan"
      True "Semantic corner case: the empty plan is available and consumes no budget."
      "semantic-case" "empty-plan" (Just 1)
      0 manualEmptyPlanModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkBudgetCase mode "budget-manual-vacuous-precondition" "manual-vacuous-precondition"
      True "Semantic corner case: the precondition is false everywhere, so the budget condition is vacuous."
      "semantic-case" "vacuous-precondition" (Just 1)
      0 manualVacuousPreconditionModel agentOne (B.BProp unusedProp) (B.BProp goalProp)

  , mkBudgetCase mode "budget-manual-within-budget" "manual-within-budget"
      True "A two-step plan reaches the goal and exactly fits the available budget."
      "semantic-case" "within-budget" (Just 3)
      2 manualWithinBudgetModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkBudgetCase mode "budget-manual-over-budget" "manual-over-budget"
      False "The same two-step plan is available and reaches the goal, but it exceeds the budget."
      "semantic-case" "over-budget" Nothing
      1 manualWithinBudgetModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkBudgetCase mode "budget-manual-unaware-cheap-action" "manual-unaware-cheap-action"
      False "A cheap safe action exists in the LTS, but the agent's only available class uses an expensive action."
      "semantic-case" "unaware-cheap-action" Nothing
      1 manualUnawareCheapActionModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkVectorCase mode "budget-vector-manual-within-budget" "vector-manual-within-budget"
      True "Vector-budget corner case: the plan fits both resource dimensions."
      "semantic-case" "vector-within-budget" (Just 3)
      [2, 2] manualVectorWithinBudgetModel agentOne (B.VBProp startProp) (B.VBProp goalProp)

  , mkVectorCase mode "budget-vector-manual-first-dim-failure" "vector-manual-first-dim-failure"
      False "Vector-budget corner case: the plan violates the first resource dimension."
      "semantic-case" "vector-first-dim-failure" Nothing
      [1, 2] manualVectorWithinBudgetModel agentOne (B.VBProp startProp) (B.VBProp goalProp)

  , mkVectorCase mode "budget-vector-manual-second-dim-failure" "vector-manual-second-dim-failure"
      False "Vector-budget corner case: the plan violates the second resource dimension."
      "semantic-case" "vector-second-dim-failure" Nothing
      [2, 1] manualVectorSecondDimCostModel agentOne (B.VBProp startProp) (B.VBProp goalProp)
  ]

caseStudyBenchmarks :: BenchMode -> [BenchCase]
caseStudyBenchmarks mode =
  [ mkBudgetCase mode "budget-delivery-cheap-route-positive" "delivery-cheap-route"
      True "Delivery case study: a cheap route reaches the destination within the available budget."
      "case-study" "cheap-route" (Just 4)
      3 deliveryCheapRouteModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkBudgetCase mode "budget-delivery-expensive-only-negative" "delivery-expensive-only"
      False "Delivery case study: the destination is reachable, but the agent is only aware of an over-budget route."
      "case-study" "expensive-only" Nothing
      3 deliveryExpensiveOnlyModel agentOne (B.BProp startProp) (B.BProp goalProp)

  , mkVectorCase mode "budget-robot-time-energy-positive" "robot-time-energy-positive"
      True "Robot case study: the route fits both time and energy budgets."
      "case-study" "time-energy-positive" (Just 4)
      [3, 6] robotTimeEnergyModel agentOne (B.VBProp startProp) (B.VBProp goalProp)

  , mkVectorCase mode "budget-robot-time-energy-negative" "robot-time-energy-negative"
      False "Robot case study: the route is reachable but exceeds the energy budget."
      "case-study" "time-energy-negative" Nothing
      [3, 5] robotTimeEnergyModel agentOne (B.VBProp startProp) (B.VBProp goalProp)
  ]

generatedBenchmarks :: BenchMode -> [BenchCase]
generatedBenchmarks mode =
  concat
    [ lineBudgetPositiveBenchmarks mode
    , lineBudgetOverBudgetBenchmarks mode
    , thresholdBenchmarks mode
    , costPerStepPositiveBenchmarks mode
    , costPerStepNegativeBenchmarks mode
    , classCountGoodLastBenchmarks mode
    , classCountNoGoodBenchmarks mode
    , vectorLinePositiveBenchmarks mode
    , vectorLineOverBudgetBenchmarks mode
    , vectorDimensionPositiveBenchmarks mode
    , vectorDimensionNegativeBenchmarks mode
    , vectorTightnessBenchmarks mode
    , formulaDepthPositiveBenchmarks mode
    ]

lineBudgetPositiveBenchmarks :: BenchMode -> [BenchCase]
lineBudgetPositiveBenchmarks mode =
  [ mkBudgetCase mode ("budget-line-positive-" ++ show n) "line-positive"
      True "1D budget line baseline: budget exactly matches the path cost."
      "states" (show n) (Just n)
      (n - 1) (lineBudgetModel n 1 cheapAction) agentOne (B.BProp startProp) (B.BProp goalProp)
  | n <- lineSizes mode
  ]

lineBudgetOverBudgetBenchmarks :: BenchMode -> [BenchCase]
lineBudgetOverBudgetBenchmarks mode =
  [ mkBudgetCase mode ("budget-line-over-budget-" ++ show n) "line-over-budget"
      False "1D budget line negative baseline: the goal is reachable, but the budget is one unit too small."
      "states" (show n) Nothing
      (n - 2) (lineBudgetModel n 1 cheapAction) agentOne (B.BProp startProp) (B.BProp goalProp)
  | n <- lineSizes mode
  ]

thresholdBenchmarks :: BenchMode -> [BenchCase]
thresholdBenchmarks mode =
  [ mkBudgetCase mode ("budget-threshold-b" ++ show b) "threshold"
      (b >= fixedThresholdCost)
      "Budget threshold sweep with fixed model and fixed witness length."
      "budget" (show b) (if b >= fixedThresholdCost then Just fixedThresholdWitnessSize else Nothing)
      b thresholdModel agentOne (B.BProp startProp) (B.BProp goalProp)
  | b <- thresholdBudgets mode
  ]

costPerStepPositiveBenchmarks :: BenchMode -> [BenchCase]
costPerStepPositiveBenchmarks mode =
  [ mkBudgetCase mode ("budget-cost-per-step-positive-" ++ show c) "cost-per-step-positive"
      True "Cost-per-step sweep: the budget is scaled to match the higher per-step cost."
      "cost_per_step" (show c) (Just fixedCostWitnessSize)
      (fixedCostPathLength * c) (lineBudgetModel fixedCostStates c cheapAction) agentOne (B.BProp startProp) (B.BProp goalProp)
  | c <- stepCosts mode
  ]

costPerStepNegativeBenchmarks :: BenchMode -> [BenchCase]
costPerStepNegativeBenchmarks mode =
  [ mkBudgetCase mode ("budget-cost-per-step-negative-" ++ show c) "cost-per-step-negative"
      False "Cost-per-step sweep: the route is reachable but the budget is one unit below the required cost."
      "cost_per_step" (show c) Nothing
      (fixedCostPathLength * c - 1) (lineBudgetModel fixedCostStates c cheapAction) agentOne (B.BProp startProp) (B.BProp goalProp)
  | c <- stepCosts mode
  ]

classCountGoodLastBenchmarks :: BenchMode -> [BenchCase]
classCountGoodLastBenchmarks mode =
  [ mkBudgetCase mode ("budget-class-count-good-last-" ++ show k) "class-count-good-last"
      True "Plan-class-count sweep: many over-budget classes are available, but the last class is cheap enough."
      "automata" (show k) (Just 2)
      1 (classCountGoodLastModel k) agentOne (B.BProp startProp) (B.BProp goalProp)
  | k <- classCounts mode
  ]

classCountNoGoodBenchmarks :: BenchMode -> [BenchCase]
classCountNoGoodBenchmarks mode =
  [ mkBudgetCase mode ("budget-class-count-no-good-" ++ show k) "class-count-no-good"
      False "Plan-class-count sweep: every available class is over-budget or leads to a trap."
      "automata" (show k) Nothing
      1 (classCountNoGoodModel k) agentOne (B.BProp startProp) (B.BProp goalProp)
  | k <- classCounts mode
  ]

vectorLinePositiveBenchmarks :: BenchMode -> [BenchCase]
vectorLinePositiveBenchmarks mode =
  [ mkVectorCase mode ("budget-vector-line-positive-" ++ show n) "vector-line-positive"
      True "Vector-budget line baseline: all dimensions exactly match the path cost."
      "states" (show n) (Just n)
      (replicate fixedVectorDimension (n - 1))
      (vectorLineModel n fixedVectorDimension (replicate fixedVectorDimension 1) cheapAction)
      agentOne (B.VBProp startProp) (B.VBProp goalProp)
  | n <- vectorLineSizes mode
  ]

vectorLineOverBudgetBenchmarks :: BenchMode -> [BenchCase]
vectorLineOverBudgetBenchmarks mode =
  [ mkVectorCase mode ("budget-vector-line-over-budget-" ++ show n) "vector-line-over-budget"
      False "Vector-budget line negative baseline: the last dimension is one unit too small."
      "states" (show n) Nothing
      (replicate (fixedVectorDimension - 1) (n - 1) ++ [n - 2])
      (vectorLineModel n fixedVectorDimension (replicate fixedVectorDimension 1) cheapAction)
      agentOne (B.VBProp startProp) (B.VBProp goalProp)
  | n <- vectorLineSizes mode
  ]

vectorDimensionPositiveBenchmarks :: BenchMode -> [BenchCase]
vectorDimensionPositiveBenchmarks mode =
  [ mkVectorCase mode ("budget-vector-dimension-positive-" ++ show d) "vector-dimension-positive"
      True "Vector-dimension sweep: the same route fits every resource dimension."
      "budget_dimension" (show d) (Just fixedVectorDimWitnessSize)
      (replicate d fixedVectorDimCost)
      (vectorLineModel fixedVectorDimStates d (replicate d 1) cheapAction)
      agentOne (B.VBProp startProp) (B.VBProp goalProp)
  | d <- vectorDimensions mode
  ]

vectorDimensionNegativeBenchmarks :: BenchMode -> [BenchCase]
vectorDimensionNegativeBenchmarks mode =
  [ mkVectorCase mode ("budget-vector-dimension-negative-" ++ show d) "vector-dimension-negative"
      False "Vector-dimension sweep: the last resource dimension is under-budget."
      "budget_dimension" (show d) Nothing
      (replicate (d - 1) fixedVectorDimCost ++ [fixedVectorDimCost - 1])
      (vectorLineModel fixedVectorDimStates d (replicate d 1) cheapAction)
      agentOne (B.VBProp startProp) (B.VBProp goalProp)
  | d <- vectorDimensions mode
  ]

vectorTightnessBenchmarks :: BenchMode -> [BenchCase]
vectorTightnessBenchmarks mode =
  [ mkVectorCase mode ("budget-vector-tightness-b" ++ show b) "vector-tightness"
      (b >= fixedVectorTightCost)
      "Vector-budget tightness sweep: only the second resource bound varies."
      "second_budget" (show b) (if b >= fixedVectorTightCost then Just fixedVectorTightWitnessSize else Nothing)
      [fixedVectorTightCost, b]
      vectorTightnessModel
      agentOne (B.VBProp startProp) (B.VBProp goalProp)
  | b <- vectorTightBudgets mode
  ]

formulaDepthPositiveBenchmarks :: BenchMode -> [BenchCase]
formulaDepthPositiveBenchmarks mode =
  [ mkBudgetCase mode ("budget-formula-depth-positive-" ++ show d) "formula-depth-positive"
      True "Formula-size sweep with fixed model, fixed budget, and fixed witness automaton."
      "formula_depth" (show d) (Just fixedFormulaWitnessSize)
      fixedFormulaBudget formulaDepthModel agentOne (deepDisj d (B.BProp startProp)) (deepDisj d (B.BProp goalProp))
  | d <- formulaDepths mode
  ]

lineSizes :: BenchMode -> [Int]
lineSizes Quick = [8, 16, 32]
lineSizes Full  = [16, 24, 32]

thresholdBudgets :: BenchMode -> [Int]
thresholdBudgets Quick = [0, 4, fixedThresholdCost]
thresholdBudgets Full  = [0, 4, 8, fixedThresholdCost - 1, fixedThresholdCost, fixedThresholdCost + 1]

stepCosts :: BenchMode -> [Int]
stepCosts Quick = [1, 2, 4]
stepCosts Full  = [1, 2, 4, 8]

classCounts :: BenchMode -> [Int]
classCounts Quick = [2, 4, 8]
classCounts Full  = [2, 4, 8, 12]

vectorLineSizes :: BenchMode -> [Int]
vectorLineSizes Quick = [8, 16, 32]
vectorLineSizes Full  = [16, 24, 32]

vectorDimensions :: BenchMode -> [Int]
vectorDimensions Quick = [1, 2, 3]
vectorDimensions Full  = [1, 2, 3, 4]

vectorTightBudgets :: BenchMode -> [Int]
vectorTightBudgets Quick = [0, 4, fixedVectorTightCost]
vectorTightBudgets Full  = [0, 4, fixedVectorTightCost - 1, fixedVectorTightCost, fixedVectorTightCost + 1]

formulaDepths :: BenchMode -> [Int]
formulaDepths Quick = [32, 64, 128]
formulaDepths Full  = [64, 128, 256]

fixedThresholdStates :: Int
fixedThresholdStates = 17

fixedThresholdCost :: Int
fixedThresholdCost = fixedThresholdStates - 1

fixedThresholdWitnessSize :: Int
fixedThresholdWitnessSize = fixedThresholdStates

fixedCostStates :: Int
fixedCostStates = 17

fixedCostPathLength :: Int
fixedCostPathLength = fixedCostStates - 1

fixedCostWitnessSize :: Int
fixedCostWitnessSize = fixedCostStates

fixedVectorDimension :: Int
fixedVectorDimension = 2

fixedVectorDimStates :: Int
fixedVectorDimStates = 13

fixedVectorDimCost :: Int
fixedVectorDimCost = fixedVectorDimStates - 1

fixedVectorDimWitnessSize :: Int
fixedVectorDimWitnessSize = fixedVectorDimStates

fixedVectorTightStates :: Int
fixedVectorTightStates = 17

fixedVectorTightCost :: Int
fixedVectorTightCost = fixedVectorTightStates - 1

fixedVectorTightWitnessSize :: Int
fixedVectorTightWitnessSize = fixedVectorTightStates

fixedFormulaStates :: Int
fixedFormulaStates = 16

fixedFormulaBudget :: Int
fixedFormulaBudget = fixedFormulaStates - 1

fixedFormulaWitnessSize :: Int
fixedFormulaWitnessSize = fixedFormulaStates

mkBudgetCase ::
     BenchMode
  -> String
  -> String
  -> Bool
  -> String
  -> String
  -> String
  -> Maybe Int
  -> B.Budget
  -> B.BudgetRegLTSU
  -> Int
  -> B.BudgetRegForm
  -> B.BudgetRegForm
  -> BenchCase
mkBudgetCase mode name family expected purpose primaryParameter parameterValue expectedWitness budget model agent pre goal =
  BenchCase
    { caseName            = name
    , caseLogic           = "budget"
    , caseFamily          = family
    , caseMode            = mode
    , caseExpected        = Just expected
    , caseStates          = length (B.statesBR model)
    , caseActions         = length (actionsOfBR model)
    , caseTransitions     = transitionCountBR model
    , casePropositions    = propositionCountBR model pre goal
    , caseAgents          = Just (agentCountBR model)
    , caseAutomata        = Just (automataCountBR model)
    , caseAutomatonStates = Just (automatonStateCountBR model)
    , caseBudgetDim       = Just 1
    , caseFormulaSize     = budgetFormulaSize (B.BKHI budget agent pre goal)
    , caseRun             = pure (budgetOutcome purpose primaryParameter parameterValue expectedWitness budget model agent pre goal)
    }

mkVectorCase ::
     BenchMode
  -> String
  -> String
  -> Bool
  -> String
  -> String
  -> String
  -> Maybe Int
  -> B.VectorBudget
  -> B.VectorBudgetRegLTSU
  -> Int
  -> B.VectorBudgetRegForm
  -> B.VectorBudgetRegForm
  -> BenchCase
mkVectorCase mode name family expected purpose primaryParameter parameterValue expectedWitness budget model agent pre goal =
  BenchCase
    { caseName            = name
    , caseLogic           = "budget"
    , caseFamily          = family
    , caseMode            = mode
    , caseExpected        = Just expected
    , caseStates          = length (B.statesVBR model)
    , caseActions         = length (actionsOfVBR model)
    , caseTransitions     = transitionCountVBR model
    , casePropositions    = propositionCountVBR model pre goal
    , caseAgents          = Just (agentCountVBR model)
    , caseAutomata        = Just (automataCountVBR model)
    , caseAutomatonStates = Just (automatonStateCountVBR model)
    , caseBudgetDim       = Just (length budget)
    , caseFormulaSize     = vectorFormulaSize (B.VBKHI budget agent pre goal)
    , caseRun             = pure (vectorOutcome purpose primaryParameter parameterValue expectedWitness budget model agent pre goal)
    }

budgetOutcome :: String -> String -> String -> Maybe Int -> B.Budget -> B.BudgetRegLTSU -> Int -> B.BudgetRegForm -> B.BudgetRegForm -> BenchOutcome
budgetOutcome purpose primaryParameter parameterValue expectedWitness budget model agent pre goal =
  BenchOutcome
    { outcomeResult                  = result
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomePurpose                 = Just purpose
    , outcomePrimaryParameter        = Just primaryParameter
    , outcomeParameterValue          = Just parameterValue
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (B.relationsBR model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (B.relationsBR model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedWitness
    , outcomeWitnessSizePassed       = witnessSizePassed expectedWitness witnessSize
    }
  where
    preStates =
      B.truthSetBR model pre

    goalStates =
      B.truthSetBR model goal

    witness =
      B.findWitnessAutomatonBR model budget agent pre goal

    witnessFound =
      case witness of
        Nothing -> False
        Just _  -> True

    witnessSize =
      fmap (length . autStates) witness

    result =
      case witness of
        Nothing ->
          False
        Just aut ->
          budgetWitnessSound model budget aut pre goal

vectorOutcome :: String -> String -> String -> Maybe Int -> B.VectorBudget -> B.VectorBudgetRegLTSU -> Int -> B.VectorBudgetRegForm -> B.VectorBudgetRegForm -> BenchOutcome
vectorOutcome purpose primaryParameter parameterValue expectedWitness budget model agent pre goal =
  BenchOutcome
    { outcomeResult                  = result
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomePurpose                 = Just purpose
    , outcomePrimaryParameter        = Just primaryParameter
    , outcomeParameterValue          = Just parameterValue
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (B.relationsVBR model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (B.relationsVBR model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedWitness
    , outcomeWitnessSizePassed       = witnessSizePassed expectedWitness witnessSize
    }
  where
    preStates =
      B.truthSetVBR model pre

    goalStates =
      B.truthSetVBR model goal

    witness =
      B.findWitnessAutomatonVBR model budget agent pre goal

    witnessFound =
      case witness of
        Nothing -> False
        Just _  -> True

    witnessSize =
      fmap (length . autStates) witness

    result =
      case witness of
        Nothing ->
          False
        Just aut ->
          vectorWitnessSound model budget aut pre goal

budgetWitnessSound :: B.BudgetRegLTSU -> B.Budget -> Automaton -> B.BudgetRegForm -> B.BudgetRegForm -> Bool
budgetWitnessSound model budget aut pre goal =
  R.checkCond1 plain aut preStates
  && R.checkCond2 plain aut preStates negGoalStates
  && B.checkCond3Budget1D model aut budget preStates
  where
    plain =
      B.forgetBudget model

    preStates =
      B.truthSetBR model pre

    negGoalStates =
      B.truthSetBR model (B.BNot goal)

vectorWitnessSound :: B.VectorBudgetRegLTSU -> B.VectorBudget -> Automaton -> B.VectorBudgetRegForm -> B.VectorBudgetRegForm -> Bool
vectorWitnessSound model budget aut pre goal =
  R.checkCond1 plain aut preStates
  && R.checkCond2 plain aut preStates negGoalStates
  && B.checkCond3VectorBudget model aut budget preStates
  where
    plain =
      B.forgetVectorBudget model

    preStates =
      B.truthSetVBR model pre

    negGoalStates =
      B.truthSetVBR model (B.VBNot goal)

witnessSizePassed :: Maybe Int -> Maybe Int -> Maybe Bool
witnessSizePassed Nothing _ =
  Nothing
witnessSizePassed (Just expected) actual =
  Just (actual == Just expected)

ordinaryReachable :: [(Int, [(Int, Int)])] -> [Int] -> [Int] -> Maybe Bool
ordinaryReachable _ [] _ =
  Nothing
ordinaryReachable _ _ [] =
  Nothing
ordinaryReachable relations preStates goalStates =
  Just (any reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates relations s)

ordinaryAllPreReachable :: [(Int, [(Int, Int)])] -> [Int] -> [Int] -> Maybe Bool
ordinaryAllPreReachable _ [] _ =
  Nothing
ordinaryAllPreReachable _ _ [] =
  Nothing
ordinaryAllPreReachable relations preStates goalStates =
  Just (all reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates relations s)

reachableStates :: [(Int, [(Int, Int)])] -> Int -> [Int]
reachableStates relations start =
  go [] [start]
  where
    edges =
      nub (concatMap snd relations)

    successors s =
      [v | (u, v) <- edges, u == s]

    go visited [] =
      visited

    go visited (x:queue)
      | x `elem` visited =
          go visited queue
      | otherwise =
          go (x:visited) (queue ++ successors x)

manualEmptyPlanModel :: B.BudgetRegLTSU
manualEmptyPlanModel =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1]
    , B.relationsBR = []
    , B.uncertaintyBR = [(agentOne, [emptyPlanAutomaton])]
    , B.weightsBR = []
    , B.valuationBR = [(0, [startProp, goalProp]), (1, [])]
    }

manualVacuousPreconditionModel :: B.BudgetRegLTSU
manualVacuousPreconditionModel =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1]
    , B.relationsBR = []
    , B.uncertaintyBR = [(agentOne, [emptyPlanAutomaton])]
    , B.weightsBR = []
    , B.valuationBR = [(0, []), (1, [goalProp])]
    }

manualWithinBudgetModel :: B.BudgetRegLTSU
manualWithinBudgetModel =
  lineBudgetModel 3 1 cheapAction

manualUnawareCheapActionModel :: B.BudgetRegLTSU
manualUnawareCheapActionModel =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1, 2]
    , B.relationsBR =
        [ (cheapAction, [(0, 1), (1, 1), (2, 2)])
        , (expensiveAction, [(0, 2), (1, 1), (2, 2)])
        ]
    , B.uncertaintyBR = [(agentOne, [singleActionAutomaton expensiveAction])]
    , B.weightsBR =
        [ ((0, cheapAction), -1)
        , ((1, cheapAction), 0)
        , ((2, cheapAction), 0)
        , ((0, expensiveAction), -10)
        , ((1, expensiveAction), 0)
        , ((2, expensiveAction), 0)
        ]
    , B.valuationBR = [(0, [startProp]), (1, [goalProp]), (2, [])]
    }

manualVectorWithinBudgetModel :: B.VectorBudgetRegLTSU
manualVectorWithinBudgetModel =
  vectorLineModel 3 2 [1, 1] cheapAction

manualVectorSecondDimCostModel :: B.VectorBudgetRegLTSU
manualVectorSecondDimCostModel =
  vectorLineModel 3 2 [1, 2] cheapAction

deliveryCheapRouteModel :: B.BudgetRegLTSU
deliveryCheapRouteModel =
  lineBudgetModel 4 1 cheapAction

deliveryExpensiveOnlyModel :: B.BudgetRegLTSU
deliveryExpensiveOnlyModel =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1, 2, 3]
    , B.relationsBR =
        [ (cheapAction, [(0, 1), (1, 2), (2, 3)])
        , (expensiveAction, [(0, 1), (1, 2), (2, 3)])
        ]
    , B.uncertaintyBR = [(agentOne, [lineAutomaton 4 expensiveAction])]
    , B.weightsBR =
        [ ((i, cheapAction), -1)
        | i <- [0 .. 2]
        ] ++
        [ ((i, expensiveAction), -3)
        | i <- [0 .. 2]
        ]
    , B.valuationBR = lineValuation 4
    }

robotTimeEnergyModel :: B.VectorBudgetRegLTSU
robotTimeEnergyModel =
  vectorLineModel 4 2 [1, 2] cheapAction

lineBudgetModel :: Int -> Int -> Int -> B.BudgetRegLTSU
lineBudgetModel n0 cost action =
  B.BudgetRegLTSU
    { B.statesBR = [0 .. n - 1]
    , B.relationsBR = [(action, [(i, i + 1) | i <- [0 .. n - 2]])]
    , B.uncertaintyBR = [(agentOne, [lineAutomaton n action])]
    , B.weightsBR = [((i, action), negate cost) | i <- [0 .. n - 2]]
    , B.valuationBR = lineValuation n
    }
  where
    n =
      max 2 n0

thresholdModel :: B.BudgetRegLTSU
thresholdModel =
  lineBudgetModel fixedThresholdStates 1 cheapAction

classCountGoodLastModel :: Int -> B.BudgetRegLTSU
classCountGoodLastModel k0 =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1, trap]
    , B.relationsBR =
        [ (a, [(0, target a), (1, 1), (trap, trap)])
        | a <- acts
        ]
    , B.uncertaintyBR = [(agentOne, [singleActionAutomaton a | a <- acts])]
    , B.weightsBR =
        [ ((0, a), if a == good then -1 else -10)
        | a <- acts
        ]
    , B.valuationBR = [(0, [startProp]), (1, [goalProp]), (trap, [])]
    }
  where
    k =
      max 2 k0

    acts =
      [1 .. k]

    good =
      k

    trap =
      k + 1

    target a =
      if a == good then 1 else trap

classCountNoGoodModel :: Int -> B.BudgetRegLTSU
classCountNoGoodModel k0 =
  B.BudgetRegLTSU
    { B.statesBR = [0, 1, trap]
    , B.relationsBR =
        [ (a, [(0, trap), (1, 1), (trap, trap)])
        | a <- acts
        ]
    , B.uncertaintyBR = [(agentOne, [singleActionAutomaton a | a <- acts])]
    , B.weightsBR =
        [ ((0, a), -10)
        | a <- acts
        ]
    , B.valuationBR = [(0, [startProp]), (1, [goalProp]), (trap, [])]
    }
  where
    k =
      max 1 k0

    acts =
      [1 .. k]

    trap =
      k + 1

vectorLineModel :: Int -> Int -> [Int] -> Int -> B.VectorBudgetRegLTSU
vectorLineModel n0 dim0 costs action =
  B.VectorBudgetRegLTSU
    { B.statesVBR = [0 .. n - 1]
    , B.relationsVBR = [(action, [(i, i + 1) | i <- [0 .. n - 2]])]
    , B.uncertaintyVBR = [(agentOne, [lineAutomaton n action])]
    , B.weightsVBR = [((i, action), map negate paddedCosts) | i <- [0 .. n - 2]]
    , B.valuationVBR = lineValuation n
    }
  where
    n =
      max 2 n0

    dim =
      max 1 dim0

    paddedCosts =
      take dim (costs ++ repeat 1)

vectorTightnessModel :: B.VectorBudgetRegLTSU
vectorTightnessModel =
  vectorLineModel fixedVectorTightStates 2 [1, 1] cheapAction

formulaDepthModel :: B.BudgetRegLTSU
formulaDepthModel =
  lineBudgetModel fixedFormulaStates 1 cheapAction

lineValuation :: Int -> [(Int, [Int])]
lineValuation n =
  [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
  | s <- [0 .. n - 1]
  ]

emptyPlanAutomaton :: Automaton
emptyPlanAutomaton =
  Automaton
    { autStates = [0]
    , autAlphabet = []
    , autTransitions = []
    , autInitial = [0]
    , autFinal = [0]
    }

singleActionAutomaton :: Int -> Automaton
singleActionAutomaton a =
  Automaton
    { autStates = [0, 1]
    , autAlphabet = [a]
    , autTransitions = [((0, a), [1])]
    , autInitial = [0]
    , autFinal = [1]
    }

lineAutomaton :: Int -> Int -> Automaton
lineAutomaton n0 a =
  Automaton
    { autStates = [0 .. n - 1]
    , autAlphabet = [a]
    , autTransitions = [((i, a), [i + 1]) | i <- [0 .. n - 2]]
    , autInitial = [0]
    , autFinal = [n - 1]
    }
  where
    n =
      max 1 n0

actionsOfBR :: B.BudgetRegLTSU -> [Int]
actionsOfBR model =
  nub [a | (a, _) <- B.relationsBR model]

actionsOfVBR :: B.VectorBudgetRegLTSU -> [Int]
actionsOfVBR model =
  nub [a | (a, _) <- B.relationsVBR model]

transitionCountBR :: B.BudgetRegLTSU -> Int
transitionCountBR model =
  sum [length rel | (_, rel) <- B.relationsBR model]

transitionCountVBR :: B.VectorBudgetRegLTSU -> Int
transitionCountVBR model =
  sum [length rel | (_, rel) <- B.relationsVBR model]

agentCountBR :: B.BudgetRegLTSU -> Int
agentCountBR model =
  length (B.uncertaintyBR model)

agentCountVBR :: B.VectorBudgetRegLTSU -> Int
agentCountVBR model =
  length (B.uncertaintyVBR model)

automataCountBR :: B.BudgetRegLTSU -> Int
automataCountBR model =
  sum [length auts | (_, auts) <- B.uncertaintyBR model]

automataCountVBR :: B.VectorBudgetRegLTSU -> Int
automataCountVBR model =
  sum [length auts | (_, auts) <- B.uncertaintyVBR model]

automatonStateCountBR :: B.BudgetRegLTSU -> Int
automatonStateCountBR model =
  sum [length (autStates aut) | (_, auts) <- B.uncertaintyBR model, aut <- auts]

automatonStateCountVBR :: B.VectorBudgetRegLTSU -> Int
automatonStateCountVBR model =
  sum [length (autStates aut) | (_, auts) <- B.uncertaintyVBR model, aut <- auts]

propositionCountBR :: B.BudgetRegLTSU -> B.BudgetRegForm -> B.BudgetRegForm -> Int
propositionCountBR model pre goal =
  length . nub $
    concatMap snd (B.valuationBR model)
    ++ budgetFormPropositions pre
    ++ budgetFormPropositions goal

propositionCountVBR :: B.VectorBudgetRegLTSU -> B.VectorBudgetRegForm -> B.VectorBudgetRegForm -> Int
propositionCountVBR model pre goal =
  length . nub $
    concatMap snd (B.valuationVBR model)
    ++ vectorFormPropositions pre
    ++ vectorFormPropositions goal

budgetFormulaSize :: B.BudgetRegForm -> Int
budgetFormulaSize (B.BProp _) =
  1
budgetFormulaSize (B.BNot f) =
  1 + budgetFormulaSize f
budgetFormulaSize (B.BDisj f g) =
  1 + budgetFormulaSize f + budgetFormulaSize g
budgetFormulaSize (B.BKHI _ _ f g) =
  1 + budgetFormulaSize f + budgetFormulaSize g

vectorFormulaSize :: B.VectorBudgetRegForm -> Int
vectorFormulaSize (B.VBProp _) =
  1
vectorFormulaSize (B.VBNot f) =
  1 + vectorFormulaSize f
vectorFormulaSize (B.VBDisj f g) =
  1 + vectorFormulaSize f + vectorFormulaSize g
vectorFormulaSize (B.VBKHI _ _ f g) =
  1 + vectorFormulaSize f + vectorFormulaSize g

budgetFormPropositions :: B.BudgetRegForm -> [Int]
budgetFormPropositions (B.BProp p) =
  [p]
budgetFormPropositions (B.BNot f) =
  budgetFormPropositions f
budgetFormPropositions (B.BDisj f g) =
  budgetFormPropositions f ++ budgetFormPropositions g
budgetFormPropositions (B.BKHI _ _ f g) =
  budgetFormPropositions f ++ budgetFormPropositions g

vectorFormPropositions :: B.VectorBudgetRegForm -> [Int]
vectorFormPropositions (B.VBProp p) =
  [p]
vectorFormPropositions (B.VBNot f) =
  vectorFormPropositions f
vectorFormPropositions (B.VBDisj f g) =
  vectorFormPropositions f ++ vectorFormPropositions g
vectorFormPropositions (B.VBKHI _ _ f g) =
  vectorFormPropositions f ++ vectorFormPropositions g

deepDisj :: Int -> B.BudgetRegForm -> B.BudgetRegForm
deepDisj n f =
  foldr B.BDisj f (replicate (max 0 n) falseBudget)

falseBudget :: B.BudgetRegForm
falseBudget =
  B.BNot (B.BDisj (B.BProp startProp) (B.BNot (B.BProp startProp)))

props :: [(Bool, Int)] -> [Int]
props xs =
  [p | (ok, p) <- xs, ok]