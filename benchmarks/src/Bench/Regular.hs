{-# OPTIONS_GHC -fno-full-laziness #-}
module Bench.Regular (regularBenchmarks) where

import Data.List (nub)

import Automata
import Bench.Common
import qualified RegKH as R

startProp :: Int
startProp = 0

goalProp :: Int
goalProp = 1

unusedProp :: Int
unusedProp = 2

goodAction :: Int
goodAction = 1

badAction :: Int
badAction = 2

safeAction :: Int
safeAction = 1

riskyAction :: Int
riskyAction = 2

rescueEnterAction :: Int
rescueEnterAction = 10

rescueLocateAction :: Int
rescueLocateAction = 11

rescueEvacuateAction :: Int
rescueEvacuateAction = 12

rescueSmokeAction :: Int
rescueSmokeAction = 13

rescueBlockedDoorAction :: Int
rescueBlockedDoorAction = 14

rescueBypassAction :: Int
rescueBypassAction = 15

agentOne :: Int
agentOne = 1

agentTwo :: Int
agentTwo = 2

regularBenchmarks :: BenchMode -> [BenchCase]
regularBenchmarks mode =
  concat
    [ manualBenchmarks mode
    , caseStudyBenchmarks mode
    , generatedBenchmarks mode
    ]

manualBenchmarks :: BenchMode -> [BenchCase]
manualBenchmarks mode =
  [ mkRegCase mode "regular-manual-empty-plan" "manual-empty-plan"
      True "Semantic corner case: the empty plan is available and the start state already satisfies the goal."
      "semantic-case" "empty-plan" (Just 1)
      manualEmptyPlanModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-vacuous-precondition" "manual-vacuous-precondition"
      True "Semantic corner case: the precondition is false everywhere, so any available plan class satisfies the requirement."
      "semantic-case" "vacuous-precondition" (Just 1)
      manualVacuousPreconditionModel agentOne (R.Prop unusedProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-single-good-class" "manual-single-good-class"
      True "The agent has one available regular plan class, and it guarantees reaching the goal."
      "semantic-case" "single-good-class" (Just 2)
      manualSingleGoodClassModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-good-bad-class" "manual-good-bad-class"
      False "The agent cannot distinguish a good one-step plan from a bad one-step plan in the same automaton class."
      "semantic-case" "good-bad-class" Nothing
      manualGoodBadClassModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-not-strongly-executable" "manual-not-strongly-executable"
      False "The automaton expects an action that is not executable from the precondition state, so strong executability fails."
      "semantic-case" "not-strongly-executable" Nothing
      manualNotSEModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-unaware-good-action" "manual-unaware-good-action"
      False "The environment has a good action, but the agent's available automata do not include it."
      "semantic-case" "unaware-good-action" Nothing
      manualUnawareGoodActionModel agentOne (R.Prop startProp) (R.Prop goalProp)
  
  
  
    , mkRegCase mode "regular-manual-trim-baseline-positive" "manual-trim-regression"
      True "Trim regression baseline: the trim automaton accepts the good one-step plan."
      "semantic-case" "trim-baseline" (Just 2)
      manualTrimBaselineModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-nontrim-garbage-branch-positive" "manual-trim-regression"
      True "Trim regression: a reachable non-productive garbage branch must not change the accepted language."
      "semantic-case" "nontrim-garbage-branch" (Just 2)
      manualNonTrimGarbageBranchModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-agent-one-knows" "manual-agent-difference"
      True "In the same model, agent 1 has a good plan class."
      "semantic-case" "agent-one" (Just 2)
      manualAgentDifferenceModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-manual-agent-two-fails" "manual-agent-difference"
      False "In the same model, agent 2 only has a risky plan class."
      "semantic-case" "agent-two" Nothing
      manualAgentDifferenceModel agentTwo (R.Prop startProp) (R.Prop goalProp)
  ]

caseStudyBenchmarks :: BenchMode -> [BenchCase]
caseStudyBenchmarks mode =
  [ mkRegCase mode "regular-baking-good-method-positive" "baking-good-method"
      True "Baking case study: the agent can identify the adequate method, represented by a singleton good plan class."
      "case-study" "good-method" (Just 2)
      bakingGoodMethodModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-baking-confused-methods-negative" "baking-confused-methods"
      False "Baking case study: the agent confuses an adequate method with a bad method in the same plan class."
      "case-study" "confused-methods" Nothing
      bakingConfusedMethodsModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-robot-aware-safe-positive" "robot-aware-safe"
      True "Robot case study: the agent is aware of a safe action class that guarantees reaching the goal."
      "case-study" "aware-safe" (Just 4)
      robotAwareSafeModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-robot-unaware-safe-negative" "robot-unaware-safe"
      False "Robot case study: the safe action exists in the LTS, but the agent is only aware of risky behaviour."
      "case-study" "unaware-safe" Nothing
      robotUnawareSafeModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-rescue-aware-route-positive" "rescue-regular"
      True "Autonomous rescue case study: the agent is aware of a regular plan class containing exactly the safe rescue route."
      "case-study" "aware-safe-rescue-route" (Just 4)
      rescueRegularAwareModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-rescue-confused-routes-negative" "rescue-regular"
      False "Autonomous rescue case study: a safe rescue route exists, but the agent confuses it with hazardous routes in the same regular plan class."
      "case-study" "confused-rescue-routes" Nothing
      rescueRegularConfusedModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-rescue-unaware-safe-route-negative" "rescue-regular"
      False "Autonomous rescue case study: the safe rescue route exists in the building, but it is absent from the agent's available regular plan classes."
      "case-study" "unaware-safe-rescue-route" Nothing
      rescueRegularUnawareModel agentOne (R.Prop startProp) (R.Prop goalProp)

  , mkRegCase mode "regular-rescue-alternative-safe-routes-positive" "rescue-regular"
      True "Autonomous rescue case study: the agent has a regular plan class containing two alternative rescue routes, and both routes are safe."
      "case-study" "alternative-safe-rescue-routes" (Just 5)
      rescueRegularAlternativeModel agentOne (R.Prop startProp) (R.Prop goalProp)
  ]

generatedBenchmarks :: BenchMode -> [BenchCase]
generatedBenchmarks mode =
  concat
    [ linePositiveBenchmarks mode
    , lineBrokenNegativeBenchmarks mode
    , automatonOnlySizePositiveBenchmarks mode
    , automatonOnlySizeNegativeBenchmarks mode
    , classCountGoodLastBenchmarks mode
    , classCountNoGoodBenchmarks mode
    , allGoodMixedClassPositiveBenchmarks mode
    , mixedClassNegativeBenchmarks mode
    , regularLanguageWidthPositiveBenchmarks mode
    , regularLanguageWidthNegativeBenchmarks mode
    , regularLanguageDepthPositiveBenchmarks mode
    , regularLanguageDepthNegativeBenchmarks mode
    , awarenessPositiveBenchmarks mode
    , basicCapableUnawareNegativeBenchmarks mode
    , multiAgentOneKnowsBenchmarks mode
    , multiAgentLastFailsBenchmarks mode
    , formulaDepthPositiveBenchmarks mode
    ]

linePositiveBenchmarks :: BenchMode -> [BenchCase]
linePositiveBenchmarks mode =
  [ mkRegCase mode ("regular-line-positive-" ++ show n) "line-positive"
      True "Regular positive baseline: the witness automaton accepts the unique line plan."
      "states" (show n) (Just n)
      (regularLinePositiveModel n) agentOne (R.Prop startProp) (R.Prop goalProp)
  | n <- lineSizes mode
  ]

lineBrokenNegativeBenchmarks :: BenchMode -> [BenchCase]
lineBrokenNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-line-broken-negative-" ++ show n) "line-broken-negative"
      False "Regular negative baseline: the automaton accepts a line plan that stops before the goal."
      "states" (show n) Nothing
      (regularLineBrokenModel n) agentOne (R.Prop startProp) (R.Prop goalProp)
  | n <- lineSizes mode
  ]

automatonOnlySizePositiveBenchmarks :: BenchMode -> [BenchCase]
automatonOnlySizePositiveBenchmarks mode =
  [ mkRegCase mode ("regular-automaton-only-size-positive-" ++ show q) "automaton-only-size-positive"
      True "Automaton-only sweep: the LTS is fixed while the automaton contains additional unreachable states."
      "automaton_states" (show q') (Just fixedAutomatonLtsSize)
      (automatonOnlyPositiveModel q') agentOne (R.Prop startProp) (R.Prop goalProp)
  | q <- automatonOnlySizes mode
  , let q' = max fixedAutomatonLtsSize q
  ]

automatonOnlySizeNegativeBenchmarks :: BenchMode -> [BenchCase]
automatonOnlySizeNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-automaton-only-size-negative-" ++ show q) "automaton-only-size-negative"
      False "Automaton-only negative sweep: the LTS has a safe path, but the agent's automaton accepts only the risky action."
      "automaton_states" (show q') Nothing
      (automatonOnlyNegativeModel q') agentOne (R.Prop startProp) (R.Prop goalProp)
  | q <- automatonOnlySizes mode
  , let q' = max fixedAutomatonLtsSize q
  ]

classCountGoodLastBenchmarks :: BenchMode -> [BenchCase]
classCountGoodLastBenchmarks mode =
  [ mkRegCase mode ("regular-class-count-good-last-" ++ show k) "class-count-good-last"
      True "Plan-class-count sweep: many bad singleton classes are available, but the last class is good."
      "automata" (show k) (Just 2)
      (classCountGoodLastModel k) agentOne (R.Prop startProp) (R.Prop goalProp)
  | k <- classCounts mode
  ]

classCountNoGoodBenchmarks :: BenchMode -> [BenchCase]
classCountNoGoodBenchmarks mode =
  [ mkRegCase mode ("regular-class-count-no-good-" ++ show k) "class-count-no-good"
      False "Plan-class-count sweep: all available singleton classes lead to a trap."
      "automata" (show k) Nothing
      (classCountNoGoodModel k) agentOne (R.Prop startProp) (R.Prop goalProp)
  | k <- classCounts mode
  ]

allGoodMixedClassPositiveBenchmarks :: BenchMode -> [BenchCase]
allGoodMixedClassPositiveBenchmarks mode =
  [ mkRegCase mode ("regular-all-good-mixed-class-positive-" ++ show k) "all-good-mixed-class-positive"
      True "Plan-class-size positive sweep: one automaton class contains several distinct actions, all of which guarantee the goal."
      "class_size" (show k) (Just 2)
      (allGoodMixedClassModel k) agentOne (R.Prop startProp) (R.Prop goalProp)
  | k <- mixedClassSizes mode
  ]

mixedClassNegativeBenchmarks :: BenchMode -> [BenchCase]
mixedClassNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-mixed-class-negative-" ++ show k) "mixed-class-negative"
      False "Plan-class-size negative sweep: one automaton class contains one good action and several bad actions."
      "class_size" (show k) Nothing
      (mixedClassModel k) agentOne (R.Prop startProp) (R.Prop goalProp)
  | k <- mixedClassSizes mode
  ]

regularLanguageWidthPositiveBenchmarks :: BenchMode -> [BenchCase]
regularLanguageWidthPositiveBenchmarks mode =
  [ mkRegCase mode ("regular-language-width-positive-w" ++ show w) "regular-language-width-positive"
      True "Regular-language width sweep: one automaton accepts many length-d plans, and every accepted plan reaches the goal."
      "width" (show w) (Just (fixedLanguageDepth + 1))
      (regularLanguageBranchingPositiveModel fixedLanguageDepth w) agentOne (R.Prop startProp) (R.Prop goalProp)
  | w <- languageWidths mode
  ]

regularLanguageWidthNegativeBenchmarks :: BenchMode -> [BenchCase]
regularLanguageWidthNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-language-width-negative-w" ++ show w) "regular-language-width-negative"
      False "Regular-language width sweep: one automaton accepts many length-d plans, but one accepted action can enter a trap."
      "width" (show w) Nothing
      (regularLanguageBranchingNegativeModel fixedLanguageDepth w) agentOne (R.Prop startProp) (R.Prop goalProp)
  | w <- languageWidths mode
  ]

regularLanguageDepthPositiveBenchmarks :: BenchMode -> [BenchCase]
regularLanguageDepthPositiveBenchmarks mode =
  [ mkRegCase mode ("regular-language-depth-positive-d" ++ show d) "regular-language-depth-positive"
      True "Regular-language depth sweep: branching width is fixed while accepted plan length increases."
      "depth" (show d) (Just (d + 1))
      (regularLanguageBranchingPositiveModel d fixedLanguageWidth) agentOne (R.Prop startProp) (R.Prop goalProp)
  | d <- languageDepths mode
  ]

regularLanguageDepthNegativeBenchmarks :: BenchMode -> [BenchCase]
regularLanguageDepthNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-language-depth-negative-d" ++ show d) "regular-language-depth-negative"
      False "Regular-language depth sweep: branching width is fixed, but one accepted branch can enter a trap."
      "depth" (show d) Nothing
      (regularLanguageBranchingNegativeModel d fixedLanguageWidth) agentOne (R.Prop startProp) (R.Prop goalProp)
  | d <- languageDepths mode
  ]

awarenessPositiveBenchmarks :: BenchMode -> [BenchCase]
awarenessPositiveBenchmarks mode =
  [ mkRegCase mode ("regular-awareness-positive-" ++ show n) "awareness-positive"
      True "Awareness sweep: the safe action is present in the agent's automaton."
      "path_length" (show (n - 1)) (Just n)
      (awarenessPositiveModel n) agentOne (R.Prop startProp) (R.Prop goalProp)
  | n <- awarenessSizes mode
  ]

basicCapableUnawareNegativeBenchmarks :: BenchMode -> [BenchCase]
basicCapableUnawareNegativeBenchmarks mode =
  [ mkRegCase mode ("regular-basic-capable-unaware-negative-" ++ show n) "basic-capable-unaware-negative"
      False "Basic-capable but unaware: the safe plan exists in the LTS, but it is absent from the queried agent's available plan classes."
      "path_length" (show (n - 1)) Nothing
      (awarenessNegativeModel n) agentOne (R.Prop startProp) (R.Prop goalProp)
  | n <- awarenessSizes mode
  ]

multiAgentOneKnowsBenchmarks :: BenchMode -> [BenchCase]
multiAgentOneKnowsBenchmarks mode =
  [ mkRegCase mode ("regular-multi-agent-one-knows-" ++ show k) "multi-agent-one-knows"
      True "Multi-agent semantic sweep: the queried agent has a good plan class."
      "agents" (show k) (Just 2)
      (multiAgentModel k) agentOne (R.Prop startProp) (R.Prop goalProp)
  | k <- agentCounts mode
  ]

multiAgentLastFailsBenchmarks :: BenchMode -> [BenchCase]
multiAgentLastFailsBenchmarks mode =
  [ mkRegCase mode ("regular-multi-agent-last-fails-" ++ show k) "multi-agent-last-fails"
      False "Multi-agent semantic sweep: the queried last agent only has a bad plan class."
      "agents" (show k) Nothing
      (multiAgentModel k) k (R.Prop startProp) (R.Prop goalProp)
  | k <- agentCounts mode
  ]

formulaDepthPositiveBenchmarks :: BenchMode -> [BenchCase]
formulaDepthPositiveBenchmarks mode =
  [ mkRegCase mode ("regular-formula-depth-positive-" ++ show d) "formula-depth-positive"
      True "Formula-size sweep with fixed model and fixed witness automaton."
      "formula_depth" (show d) (Just fixedFormulaAutomatonStates)
      formulaDepthModel agentOne (deepDisj d (R.Prop startProp)) (deepDisj d (R.Prop goalProp))
  | d <- formulaDepths mode
  ]

lineSizes :: BenchMode -> [Int]
lineSizes Quick = [8, 16, 32]
lineSizes Full  = [16, 32, 64, 128]

automatonOnlySizes :: BenchMode -> [Int]
automatonOnlySizes Quick = [32, 48, 64]
automatonOnlySizes Full  = [32, 64, 128, 256]

classCounts :: BenchMode -> [Int]
classCounts Quick = [2, 4, 8]
classCounts Full  = [2, 4, 8, 12, 16]

mixedClassSizes :: BenchMode -> [Int]
mixedClassSizes Quick = [2, 4, 8]
mixedClassSizes Full  = [2, 4, 8, 12, 16]

languageWidths :: BenchMode -> [Int]
languageWidths Quick = [2, 3, 4]
languageWidths Full  = [2, 3, 4, 5, 6]

languageDepths :: BenchMode -> [Int]
languageDepths Quick = [4, 6, 8]
languageDepths Full  = [4, 6, 8, 10, 12]

awarenessSizes :: BenchMode -> [Int]
awarenessSizes Quick = [8, 16, 32]
awarenessSizes Full  = [16, 32, 64, 128]

agentCounts :: BenchMode -> [Int]
agentCounts Quick = [2, 3, 4]
agentCounts Full  = [2, 4, 8, 12]

formulaDepths :: BenchMode -> [Int]
formulaDepths Quick = [32, 64, 128]
formulaDepths Full  = [64, 128, 256, 512]

fixedAutomatonLtsSize :: Int
fixedAutomatonLtsSize = 32

fixedLanguageDepth :: Int
fixedLanguageDepth = 8

fixedLanguageWidth :: Int
fixedLanguageWidth = 3

fixedFormulaAutomatonStates :: Int
fixedFormulaAutomatonStates = 32

mkRegCase ::
     BenchMode
  -> String
  -> String
  -> Bool
  -> String
  -> String
  -> String
  -> Maybe Int
  -> R.RegLTSU
  -> R.Agent
  -> R.RegForm
  -> R.RegForm
  -> BenchCase
mkRegCase mode name family expected purpose primaryParameter parameterValue expectedWitness model agent pre goal =
  BenchCase
    { caseName                 = name
    , caseLogic                = "regular"
    , caseFamily               = family
    , caseMode                 = mode
    , caseExpected             = Just expected
    , caseStates               = length (R.statesM model)
    , caseActions              = length (actionsOfReg model)
    , caseTransitions          = transitionCount model
    , casePropositions         = propositionCount model pre goal
    , caseAgents               = Just (agentCount model)
    , caseAutomata             = Just (automataCount model)
    , caseAutomatonStates      = Just (automatonStateCount model)
    , caseAutomatonTransitions = Just (automatonTransitionCount model)
    , caseBudgetDim            = Nothing
    , caseFormulaSize          = regFormulaSize (R.KHI agent pre goal)
    , caseRun                  = pure (regOutcome purpose primaryParameter parameterValue expectedWitness model agent pre goal)
    }

regOutcome :: String -> String -> String -> Maybe Int -> R.RegLTSU -> R.Agent -> R.RegForm -> R.RegForm -> BenchOutcome
regOutcome purpose primaryParameter parameterValue expectedWitness model agent pre goal =
  BenchOutcome
    { outcomeResult                  = result
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomeWitnessAgrees           = Nothing
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
      R.truthSet model pre

    goalStates =
      R.truthSet model goal

    witness =
      R.findWitnessAutomaton model agent pre goal

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
          witnessAutomatonSound model aut pre goal

witnessAutomatonSound :: R.RegLTSU -> Automaton -> R.RegForm -> R.RegForm -> Bool
witnessAutomatonSound model aut pre goal =
  R.checkCond1 model aut preStates
  && R.checkCond2 model aut preStates negGoalStates
  where
    preStates =
      R.truthSet model pre

    negGoalStates =
      R.truthSet model (R.Not goal)

witnessSizePassed :: Maybe Int -> Maybe Int -> Maybe Bool
witnessSizePassed Nothing _ =
  Nothing
witnessSizePassed (Just expected) actual =
  Just (actual == Just expected)

ordinaryReachable :: R.RegLTSU -> [Int] -> [Int] -> Maybe Bool
ordinaryReachable _ [] _ =
  Nothing
ordinaryReachable _ _ [] =
  Nothing
ordinaryReachable model preStates goalStates =
  Just (any reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates model s)

ordinaryAllPreReachable :: R.RegLTSU -> [Int] -> [Int] -> Maybe Bool
ordinaryAllPreReachable _ [] _ =
  Nothing
ordinaryAllPreReachable _ _ [] =
  Nothing
ordinaryAllPreReachable model preStates goalStates =
  Just (all reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates model s)

reachableStates :: R.RegLTSU -> Int -> [Int]
reachableStates model start =
  go [] [start]
  where
    edges =
      nub (concatMap snd (R.relationsM model))

    successors s =
      [v | (u, v) <- edges, u == s]

    go visited [] =
      visited

    go visited (x:queue)
      | x `elem` visited =
          go visited queue
      | otherwise =
          go (x:visited) (queue ++ successors x)

manualEmptyPlanModel :: R.RegLTSU
manualEmptyPlanModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM = []
    , R.uncertainty = [(agentOne, [emptyPlanAutomaton])]
    , R.valuationM = [(0, [startProp, goalProp]), (1, [])]
    }

manualVacuousPreconditionModel :: R.RegLTSU
manualVacuousPreconditionModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM = []
    , R.uncertainty = [(agentOne, [emptyPlanAutomaton])]
    , R.valuationM = [(0, []), (1, [goalProp])]
    }

manualSingleGoodClassModel :: R.RegLTSU
manualSingleGoodClassModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM = [(goodAction, [(0, 1), (1, 1)])]
    , R.uncertainty = [(agentOne, [singleActionAutomaton goodAction])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp])]
    }

manualGoodBadClassModel :: R.RegLTSU
manualGoodBadClassModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1), (2, 2)])
        , (badAction,  [(0, 2), (1, 1), (2, 2)])
        ]
    , R.uncertainty = [(agentOne, [oneStepChoiceAutomaton [goodAction, badAction]])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (2, [])]
    }

manualNotSEModel :: R.RegLTSU
manualNotSEModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM = [(goodAction, [(0, 1)])]
    , R.uncertainty = [(agentOne, [singleActionAutomaton badAction])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp])]
    }

manualUnawareGoodActionModel :: R.RegLTSU
manualUnawareGoodActionModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1), (2, 2)])
        , (badAction,  [(0, 2), (1, 1), (2, 2)])
        ]
    , R.uncertainty = [(agentOne, [singleActionAutomaton badAction])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (2, [])]
    }

manualTrimBaselineModel :: R.RegLTSU
manualTrimBaselineModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1)])
        ]
    , R.uncertainty =
        [ (agentOne, [singleActionAutomaton goodAction])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [goalProp])
        ]
    }

manualNonTrimGarbageBranchModel :: R.RegLTSU
manualNonTrimGarbageBranchModel =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1)])
        ]
    , R.uncertainty =
        [ (agentOne, [nonTrimGarbageBranchAutomaton goodAction badAction])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [goalProp])
        ]
    }

manualAgentDifferenceModel :: R.RegLTSU
manualAgentDifferenceModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1), (2, 2)])
        , (badAction,  [(0, 2), (1, 1), (2, 2)])
        ]
    , R.uncertainty =
        [ (agentOne, [singleActionAutomaton goodAction])
        , (agentTwo, [singleActionAutomaton badAction])
        ]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (2, [])]
    }

bakingGoodMethodModel :: R.RegLTSU
bakingGoodMethodModel =
  manualSingleGoodClassModel

bakingConfusedMethodsModel :: R.RegLTSU
bakingConfusedMethodsModel =
  manualGoodBadClassModel

robotAwareSafeModel :: R.RegLTSU
robotAwareSafeModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4]
    , R.relationsM =
        [ (safeAction,  [(0, 1), (1, 2), (2, 3), (3, 3), (4, 4)])
        , (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)])
        ]
    , R.uncertainty = [(agentOne, [sequenceAutomaton [safeAction, safeAction, safeAction]])]
    , R.valuationM = [(0, [startProp]), (1, []), (2, []), (3, [goalProp]), (4, [])]
    }

robotUnawareSafeModel :: R.RegLTSU
robotUnawareSafeModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4]
    , R.relationsM =
        [ (safeAction,  [(0, 1), (1, 2), (2, 3), (3, 3), (4, 4)])
        , (riskyAction, [(0, 1), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (4, 4)])
        ]
    , R.uncertainty = [(agentOne, [sequenceAutomaton [riskyAction, riskyAction, riskyAction]])]
    , R.valuationM = [(0, [startProp]), (1, []), (2, []), (3, [goalProp]), (4, [])]
    }

rescueRegularAwareModel :: R.RegLTSU
rescueRegularAwareModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4]
    , R.relationsM =
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
        , (rescueSmokeAction,
            [ (0, 4)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        , (rescueBlockedDoorAction,
            [ (0, 0)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        ]
    , R.uncertainty =
        [ (agentOne,
            [ sequenceAutomaton
                [ rescueEnterAction
                , rescueLocateAction
                , rescueEvacuateAction
                ]
            ])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [])
        , (2, [])
        , (3, [goalProp])
        , (4, [])
        ]
    }

rescueRegularConfusedModel :: R.RegLTSU
rescueRegularConfusedModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4]
    , R.relationsM =
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
        , (rescueSmokeAction,
            [ (0, 4)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        , (rescueBlockedDoorAction,
            [ (0, 0)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        ]
    , R.uncertainty =
        [ (agentOne,
            [ rescueConfusedRouteAutomaton
            ])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [])
        , (2, [])
        , (3, [goalProp])
        , (4, [])
        ]
    }

rescueRegularUnawareModel :: R.RegLTSU
rescueRegularUnawareModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4]
    , R.relationsM =
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
        , (rescueSmokeAction,
            [ (0, 4)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        , (rescueBlockedDoorAction,
            [ (0, 0)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            ])
        ]
    , R.uncertainty =
        [ (agentOne,
            [ sequenceAutomaton
                [ rescueSmokeAction
                , rescueLocateAction
                , rescueEvacuateAction
                ]
            , sequenceAutomaton
                [ rescueEnterAction
                , rescueBlockedDoorAction
                , rescueEvacuateAction
                ]
            ])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [])
        , (2, [])
        , (3, [goalProp])
        , (4, [])
        ]
    }

rescueRegularAlternativeModel :: R.RegLTSU
rescueRegularAlternativeModel =
  R.RegLTSU
    { R.statesM = [0, 1, 2, 3, 4, 5]
    , R.relationsM =
        [ (rescueEnterAction,
            [ (0, 1)
            , (1, 1)
            , (2, 2)
            , (3, 3)
            , (4, 4)
            , (5, 5)
            ])
        , (rescueBypassAction,
            [ (0, 0)
            , (1, 5)
            , (2, 2)
            , (3, 3)
            , (4, 4)
            , (5, 5)
            ])
        , (rescueLocateAction,
            [ (0, 0)
            , (1, 2)
            , (2, 2)
            , (3, 3)
            , (4, 4)
            , (5, 2)
            ])
        , (rescueEvacuateAction,
            [ (0, 0)
            , (1, 1)
            , (2, 3)
            , (3, 3)
            , (4, 4)
            , (5, 5)
            ])
        , (rescueSmokeAction,
            [ (0, 4)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            , (5, 4)
            ])
        , (rescueBlockedDoorAction,
            [ (0, 0)
            , (1, 4)
            , (2, 4)
            , (3, 3)
            , (4, 4)
            , (5, 4)
            ])
        ]
    , R.uncertainty =
        [ (agentOne,
            [ rescueAlternativeSafeRoutesAutomaton
            ])
        ]
    , R.valuationM =
        [ (0, [startProp])
        , (1, [])
        , (2, [])
        , (3, [goalProp])
        , (4, [])
        , (5, [])
        ]
    }

regularLinePositiveModel :: Int -> R.RegLTSU
regularLinePositiveModel n0 =
  R.RegLTSU
    { R.statesM = sts
    , R.relationsM = [(goodAction, [(i, i + 1) | i <- [0 .. n - 2]])]
    , R.uncertainty = [(agentOne, [lineAutomaton n goodAction])]
    , R.valuationM = lineValuation n
    }
  where
    n =
      max 2 n0

    sts =
      [0 .. n - 1]

regularLineBrokenModel :: Int -> R.RegLTSU
regularLineBrokenModel n0 =
  R.RegLTSU
    { R.statesM = sts
    , R.relationsM = [(goodAction, [(i, i + 1) | i <- [0 .. dead - 1]] ++ [(dead, dead)])]
    , R.uncertainty = [(agentOne, [lineAutomaton n goodAction])]
    , R.valuationM = lineValuation n
    }
  where
    n =
      max 3 n0

    dead =
      n - 2

    sts =
      [0 .. n - 1]

automatonOnlyPositiveModel :: Int -> R.RegLTSU
automatonOnlyPositiveModel q =
  R.RegLTSU
    { R.statesM = [0 .. n - 1]
    , R.relationsM = [(goodAction, [(i, i + 1) | i <- [0 .. n - 2]])]
    , R.uncertainty = [(agentOne, [paddedLineAutomaton n q goodAction])]
    , R.valuationM = lineValuation n
    }
  where
    n =
      fixedAutomatonLtsSize

automatonOnlyNegativeModel :: Int -> R.RegLTSU
automatonOnlyNegativeModel q =
  R.RegLTSU
    { R.statesM = [0 .. trap]
    , R.relationsM =
        [ (goodAction, [(i, i + 1) | i <- [0 .. n - 2]])
        , (badAction,  [(i, trap) | i <- [0 .. n - 2]] ++ [(trap, trap)])
        ]
    , R.uncertainty = [(agentOne, [paddedLineAutomaton n q badAction])]
    , R.valuationM =
        [ (s, props [(s == 0, startProp), (s == n - 1, goalProp)])
        | s <- [0 .. trap]
        ]
    }
  where
    n =
      fixedAutomatonLtsSize

    trap =
      n

classCountGoodLastModel :: Int -> R.RegLTSU
classCountGoodLastModel k0 =
  R.RegLTSU
    { R.statesM = [0, 1, trap]
    , R.relationsM =
        [ (a, [(0, target a), (1, 1), (trap, trap)])
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [singleActionAutomaton a | a <- acts])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (trap, [])]
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

classCountNoGoodModel :: Int -> R.RegLTSU
classCountNoGoodModel k0 =
  R.RegLTSU
    { R.statesM = [0, 1, trap]
    , R.relationsM =
        [ (a, [(0, trap), (1, 1), (trap, trap)])
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [singleActionAutomaton a | a <- acts])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (trap, [])]
    }
  where
    k =
      max 1 k0

    acts =
      [1 .. k]

    trap =
      k + 1

allGoodMixedClassModel :: Int -> R.RegLTSU
allGoodMixedClassModel k0 =
  R.RegLTSU
    { R.statesM = [0, 1]
    , R.relationsM =
        [ (a, [(0, 1), (1, 1)])
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [oneStepChoiceAutomaton acts])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp])]
    }
  where
    k =
      max 1 k0

    acts =
      [1 .. k]

mixedClassModel :: Int -> R.RegLTSU
mixedClassModel k0 =
  R.RegLTSU
    { R.statesM = [0, 1, trap]
    , R.relationsM =
        [ (a, [(0, target a), (1, 1), (trap, trap)])
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [oneStepChoiceAutomaton acts])]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (trap, [])]
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

regularLanguageBranchingPositiveModel :: Int -> Int -> R.RegLTSU
regularLanguageBranchingPositiveModel depth0 width0 =
  R.RegLTSU
    { R.statesM = [0 .. depth]
    , R.relationsM =
        [ (a, [(i, i + 1) | i <- [0 .. depth - 1]])
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [branchingLanguageAutomaton depth acts])]
    , R.valuationM =
        [ (s, props [(s == 0, startProp), (s == depth, goalProp)])
        | s <- [0 .. depth]
        ]
    }
  where
    depth =
      max 1 depth0

    width =
      max 1 width0

    acts =
      [1 .. width]

regularLanguageBranchingNegativeModel :: Int -> Int -> R.RegLTSU
regularLanguageBranchingNegativeModel depth0 width0 =
  R.RegLTSU
    { R.statesM = [0 .. trap]
    , R.relationsM =
        [ (a, edgesFor a)
        | a <- acts
        ]
    , R.uncertainty = [(agentOne, [branchingLanguageAutomaton depth acts])]
    , R.valuationM =
        [ (s, props [(s == 0, startProp), (s == depth, goalProp)])
        | s <- [0 .. trap]
        ]
    }
  where
    depth =
      max 1 depth0

    width =
      max 2 width0

    acts =
      [1 .. width]

    bad =
      width

    trap =
      depth + 1

    edgesFor a =
      if a == bad
        then [(i, trap) | i <- [0 .. depth - 1]] ++ [(trap, trap)]
        else [(i, i + 1) | i <- [0 .. depth - 1]] ++ [(trap, trap)]

awarenessPositiveModel :: Int -> R.RegLTSU
awarenessPositiveModel n0 =
  regularLinePositiveModel n0

awarenessNegativeModel :: Int -> R.RegLTSU
awarenessNegativeModel n0 =
  R.RegLTSU
    { R.statesM = sts
    , R.relationsM =
        [ (safeAction, [(i, i + 1) | i <- [0 .. n - 2]])
        , (riskyAction, [(i, trap) | i <- [0 .. n - 2]] ++ [(trap, trap)])
        ]
    , R.uncertainty = [(agentOne, [lineAutomaton n riskyAction])]
    , R.valuationM =
        [ (s, labels s)
        | s <- sts
        ]
    }
  where
    n =
      max 2 n0

    trap =
      n

    sts =
      [0 .. n]

    labels s =
      props [(s == 0, startProp), (s == n - 1, goalProp)]

multiAgentModel :: Int -> R.RegLTSU
multiAgentModel k0 =
  R.RegLTSU
    { R.statesM = [0, 1, trap]
    , R.relationsM =
        [ (goodAction, [(0, 1), (1, 1), (trap, trap)])
        , (badAction,  [(0, trap), (1, 1), (trap, trap)])
        ]
    , R.uncertainty =
        [ (i, [if i == 1 then singleActionAutomaton goodAction else singleActionAutomaton badAction])
        | i <- agents
        ]
    , R.valuationM = [(0, [startProp]), (1, [goalProp]), (trap, [])]
  }
  where
    k =
      max 2 k0

    agents =
      [1 .. k]

    trap =
      k + 1

formulaDepthModel :: R.RegLTSU
formulaDepthModel =
  regularLinePositiveModel fixedFormulaAutomatonStates

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

nonTrimGarbageBranchAutomaton :: Int -> Int -> Automaton
nonTrimGarbageBranchAutomaton good garbage =
  Automaton
    { autStates = [0, 1, 2]
    , autAlphabet = [good, garbage]
    , autTransitions =
        [ ((0, good), [1])
        , ((0, garbage), [2])
        , ((2, garbage), [2])
        ]
    , autInitial = [0]
    , autFinal = [1]
    }

oneStepChoiceAutomaton :: [Int] -> Automaton
oneStepChoiceAutomaton acts0 =
  Automaton
    { autStates = [0, 1]
    , autAlphabet = acts
    , autTransitions = [((0, a), [1]) | a <- acts]
    , autInitial = [0]
    , autFinal = [1]
    }
  where
    acts =
      nub acts0

sequenceAutomaton :: [Int] -> Automaton
sequenceAutomaton actions =
  Automaton
    { autStates = [0 .. n]
    , autAlphabet = nub actions
    , autTransitions = [((i, a), [i + 1]) | (i, a) <- zip [0 ..] actions]
    , autInitial = [0]
    , autFinal = [n]
    }
  where
    n =
      length actions

rescueConfusedRouteAutomaton :: Automaton
rescueConfusedRouteAutomaton =
  Automaton
    { autStates = [0, 1, 2, 3]
    , autAlphabet =
        [ rescueEnterAction
        , rescueLocateAction
        , rescueEvacuateAction
        , rescueSmokeAction
        , rescueBlockedDoorAction
        ]
    , autTransitions =
        [ ((0, rescueEnterAction), [1])
        , ((0, rescueSmokeAction), [1])
        , ((1, rescueLocateAction), [2])
        , ((1, rescueBlockedDoorAction), [2])
        , ((2, rescueEvacuateAction), [3])
        ]
    , autInitial = [0]
    , autFinal = [3]
    }

rescueAlternativeSafeRoutesAutomaton :: Automaton
rescueAlternativeSafeRoutesAutomaton =
  Automaton
    { autStates = [0, 1, 2, 3, 4]
    , autAlphabet =
        [ rescueEnterAction
        , rescueBypassAction
        , rescueLocateAction
        , rescueEvacuateAction
        ]
    , autTransitions =
        [ ((0, rescueEnterAction), [1])
        , ((1, rescueLocateAction), [2])
        , ((1, rescueBypassAction), [3])
        , ((3, rescueLocateAction), [2])
        , ((2, rescueEvacuateAction), [4])
        ]
    , autInitial = [0]
    , autFinal = [4]
    }

branchingLanguageAutomaton :: Int -> [Int] -> Automaton
branchingLanguageAutomaton depth0 acts0 =
  Automaton
    { autStates = [0 .. depth]
    , autAlphabet = acts
    , autTransitions =
        [ ((i, a), [i + 1])
        | i <- [0 .. depth - 1]
        , a <- acts
        ]
    , autInitial = [0]
    , autFinal = [depth]
    }
  where
    depth =
      max 1 depth0

    acts =
      nub acts0

lineAutomaton :: Int -> Int -> Automaton
lineAutomaton n a =
  paddedLineAutomaton n n a

paddedLineAutomaton :: Int -> Int -> Int -> Automaton
paddedLineAutomaton planStates0 totalStates0 a =
  Automaton
    { autStates = [0 .. totalStates - 1]
    , autAlphabet = [a]
    , autTransitions = [((i, a), [i + 1]) | i <- [0 .. planStates - 2]]
    , autInitial = [0]
    , autFinal = [planStates - 1]
    }
  where
    planStates =
      max 1 planStates0

    totalStates =
      max planStates totalStates0

actionsOfReg :: R.RegLTSU -> [Int]
actionsOfReg model =
  nub [a | (a, _) <- R.relationsM model]

transitionCount :: R.RegLTSU -> Int
transitionCount model =
  sum [length rel | (_, rel) <- R.relationsM model]

agentCount :: R.RegLTSU -> Int
agentCount model =
  length (R.uncertainty model)

automataCount :: R.RegLTSU -> Int
automataCount model =
  sum [length auts | (_, auts) <- R.uncertainty model]

automatonStateCount :: R.RegLTSU -> Int
automatonStateCount model =
  sum [length (autStates aut) | (_, auts) <- R.uncertainty model, aut <- auts]


propositionCount :: R.RegLTSU -> R.RegForm -> R.RegForm -> Int
propositionCount model pre goal =
  length . nub $
    concatMap snd (R.valuationM model)
    ++ regFormPropositions pre
    ++ regFormPropositions goal

regFormulaSize :: R.RegForm -> Int
regFormulaSize (R.Prop _) =
  1
regFormulaSize (R.Not f) =
  1 + regFormulaSize f
regFormulaSize (R.Disj f g) =
  1 + regFormulaSize f + regFormulaSize g
regFormulaSize (R.KHI _ f g) =
  1 + regFormulaSize f + regFormulaSize g

regFormPropositions :: R.RegForm -> [Int]
regFormPropositions (R.Prop p) =
  [p]
regFormPropositions (R.Not f) =
  regFormPropositions f
regFormPropositions (R.Disj f g) =
  regFormPropositions f ++ regFormPropositions g
regFormPropositions (R.KHI _ f g) =
  regFormPropositions f ++ regFormPropositions g

deepDisj :: Int -> R.RegForm -> R.RegForm
deepDisj n f =
  foldr R.Disj f (replicate (max 0 n) falseReg)

falseReg :: R.RegForm
falseReg =
  R.Not (R.Disj (R.Prop startProp) (R.Not (R.Prop startProp)))

props :: [(Bool, Int)] -> [Int]
props xs =
  [p | (ok, p) <- xs, ok]


automatonTransitionCount :: R.RegLTSU -> Int
automatonTransitionCount model =
  sum [length (autTransitions aut) | (_, auts) <- R.uncertainty model, aut <- auts]