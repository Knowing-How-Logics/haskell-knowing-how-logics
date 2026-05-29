{-# OPTIONS_GHC -fno-full-laziness #-}
module Bench.Random
  ( defaultRandomCases
  , randomBenchmarks
  ) where

import Control.Monad (filterM)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Test.QuickCheck (Gen, choose, elements, frequency)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Automata
import qualified BasicKH as Basic
import qualified BudgetRegKH as Budget
import Bench.Common
import qualified IntermediateKH as Intermediate
import qualified LTS as L
import qualified RegKH as Reg

defaultRandomCases :: BenchMode -> Int
defaultRandomCases Quick = 8
defaultRandomCases Full  = 24

data RandomBounds = RandomBounds
  { boundStates          :: Int
  , boundActions         :: Int
  , boundProps           :: Int
  , boundFormulaDepth    :: Int
  , boundAutomatonStates :: Int
  }

boundsFor :: BenchMode -> RandomBounds
boundsFor Quick =
  RandomBounds
    { boundStates          = 7
    , boundActions         = 3
    , boundProps           = 5
    , boundFormulaDepth    = 3
    , boundAutomatonStates = 4
    }
boundsFor Full =
  RandomBounds
    { boundStates          = 12
    , boundActions         = 5
    , boundProps           = 7
    , boundFormulaDepth    = 4
    , boundAutomatonStates = 6
    }

data CaseKind = Positive | Negative
  deriving (Eq, Show)

kindFor :: Int -> CaseKind
kindFor index
  | odd index = Positive
  | otherwise = Negative

kindName :: CaseKind -> String
kindName Positive = "positive"
kindName Negative = "negative"

expectedForKind :: CaseKind -> Bool
expectedForKind Positive = True
expectedForKind Negative = False

expectedPlanWitnessSize :: CaseKind -> Maybe Int
expectedPlanWitnessSize Positive = Just 2
expectedPlanWitnessSize Negative = Nothing

expectedAutomatonWitnessSize :: CaseKind -> Maybe Int
expectedAutomatonWitnessSize Positive = Just 3
expectedAutomatonWitnessSize Negative = Nothing

checkedResult :: Bool -> Bool -> Bool -> Bool
checkedResult expected semanticResult witnessOk
  | expected  = semanticResult && witnessOk
  | otherwise = semanticResult || not witnessOk

witnessInvariant :: Bool -> Maybe a -> (a -> Bool) -> Bool
witnessInvariant semanticResult witness sound
  | semanticResult =
      maybe False sound witness
  | otherwise =
      case witness of
        Nothing -> True
        Just _  -> False

randomBenchmarks :: BenchMode -> Int -> Int -> [BenchCase]
randomBenchmarks _ _ count
  | count <= 0 = []
randomBenchmarks mode baseSeed count =
  concat
    [ randomBasicBenchmarks mode baseSeed count
    , randomIntermediateBenchmarks mode (baseSeed + 100000) count
    , randomRegularBenchmarks mode (baseSeed + 200000) count
    , randomBudgetBenchmarks mode (baseSeed + 300000) count
    ]

runGen :: Gen a -> Int -> Int -> a
runGen gen seed size =
  unGen gen (mkQCGen seed) size

seedFor :: Int -> Int -> Int
seedFor baseSeed index =
  baseSeed + index * 7919

-- Basic random benchmark cases -------------------------------------------------

data BasicPayload = BasicPayload Bool CaseKind Basic.AbilityMap Basic.Form Basic.Form

randomBasicBenchmarks :: BenchMode -> Int -> Int -> [BenchCase]
randomBasicBenchmarks mode baseSeed count =
  [ mkRandomBasicCase mode seed i payload
  | i <- [1 .. count]
  , let seed = seedFor baseSeed i
  , let kind = kindFor i
  , let payload = runGen (genBasicPayload (boundsFor mode) kind) seed seed
  ]

mkRandomBasicCase :: BenchMode -> Int -> Int -> BasicPayload -> BenchCase
mkRandomBasicCase mode seed index (BasicPayload expectedByConstruction kind model pre goal) =
  BenchCase
    { caseName                 = "basic-random-" ++ kindName kind ++ "-seed-" ++ show seed ++ "-" ++ show index
    , caseLogic                = "basic"
    , caseFamily               = "random-basic"
    , caseMode                 = mode
    , caseExpected             = Just expectedByConstruction
    , caseStates               = basicStateCount model
    , caseActions              = length (L.actionsOf (Basic.transitions model))
    , caseTransitions          = transitionCount (Basic.transitions model)
    , casePropositions         = basicPropositionCount model pre goal
    , caseAgents               = Nothing
    , caseAutomata             = Nothing
    , caseAutomatonStates      = Nothing
    , caseAutomatonTransitions = Nothing
    , caseBudgetDim            = Nothing
    , caseFormulaSize          = basicFormulaSize (Basic.KH pre goal)
    , caseRun                  = do
        salt <- freshSalt
        pure (saltOutcome salt (basicOutcome seed kind model pre goal))
    }

genBasicPayload :: RandomBounds -> CaseKind -> Gen BasicPayload
genBasicPayload bounds Positive =
  genBasicPositivePayload bounds
genBasicPayload bounds Negative =
  genBasicNegativePayload bounds

genBasicPositivePayload :: RandomBounds -> Gen BasicPayload
genBasicPositivePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
  preStates  <- genAtMostNonEmpty 2 prePool
  midStates  <- genAtMostNonEmpty 2 midPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, s, m) | s <- preStates, m <- midStates ]
             ++ [ (a2, m, g) | m <- midStates, g <- goalStates ])
            ([ (s, a) | s <- preStates, a <- acts ]
             ++ [ (m, a) | m <- midStates, a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  pre  <- genBasicExactProp 0
  goal <- genBasicExactProp 1
  pure (BasicPayload True Positive
    Basic.LTS
      { Basic.states      = nonEmptyStates sts
      , Basic.transitions = rels
      , Basic.valuation   = vals
      }
    pre goal)

genBasicNegativePayload :: RandomBounds -> Gen BasicPayload
genBasicNegativePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      badPre = head prePool
      trap = head midPool
      a1 = head acts
      props = propsFor bounds
      preStates = [badPre]
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, badPre, trap) ]
             ++ [ (a1, badPre, g) | g <- goalStates ]
             ++ [ (a, trap, trap) | a <- acts ])
            ([ (badPre, a) | a <- acts ]
             ++ [ (trap, a) | a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  pre  <- genBasicExactProp 0
  goal <- genBasicExactProp 1
  pure (BasicPayload False Negative
    Basic.LTS
      { Basic.states      = nonEmptyStates sts
      , Basic.transitions = rels
      , Basic.valuation   = vals
      }
    pre goal)

basicOutcome :: Int -> CaseKind -> Basic.AbilityMap -> Basic.Form -> Basic.Form -> BenchOutcome
basicOutcome seed kind model pre goal =
  BenchOutcome
    { outcomeResult                  = checkedResult (expectedForKind kind) semanticResult (witnessOk && witnessSize == expectedPlanWitnessSize kind)
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomeWitnessAgrees           = Just witnessAgrees
    , outcomePurpose                 = Just ("Constrained random Basic KH " ++ kindName kind ++ " case with non-empty actions, transitions, pre, and goal.")
    , outcomePrimaryParameter        = Just "seed:kind"
    , outcomeParameterValue          = Just (show seed ++ ":" ++ kindName kind)
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (Basic.transitions model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (Basic.transitions model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedPlanWitnessSize kind
    , outcomeWitnessSizePassed       = Just (witnessSize == expectedPlanWitnessSize kind)
    }
  where
    preStates =
      Basic.truthSet model pre

    goalStates =
      Basic.truthSet model goal

    semanticResult =
      Basic.isTrue (model, NE.head (Basic.states model)) (Basic.KH pre goal)

    witness =
      Basic.findWitness model pre goal

    witnessFound =
      maybe False (const True) witness

    witnessSize =
      fmap length witness

    witnessOk =
      witnessInvariant semanticResult witness (basicWitnessSound model pre goal)

    witnessAgrees =
      witnessOk

basicWitnessSound :: Basic.AbilityMap -> Basic.Form -> Basic.Form -> L.Plan -> Bool
basicWitnessSound model pre goal plan =
  all checkState preStates
  where
    preStates =
      Basic.truthSet model pre

    goalStates =
      Basic.truthSet model goal

    rs =
      Basic.transitions model

    checkState s =
      L.stronglyExecutableAt rs s plan
      && all (`elem` goalStates) (L.executePlan rs s plan)

-- Intermediate random benchmark cases -----------------------------------------

data IntermediatePayload = IntermediatePayload Bool CaseKind Basic.AbilityMap Intermediate.IForm Intermediate.IForm Intermediate.IForm

randomIntermediateBenchmarks :: BenchMode -> Int -> Int -> [BenchCase]
randomIntermediateBenchmarks mode baseSeed count =
  [ mkRandomIntermediateCase mode seed i payload
  | i <- [1 .. count]
  , let seed = seedFor baseSeed i
  , let kind = kindFor i
  , let payload = runGen (genIntermediatePayload (boundsFor mode) kind) seed seed
  ]

mkRandomIntermediateCase :: BenchMode -> Int -> Int -> IntermediatePayload -> BenchCase
mkRandomIntermediateCase mode seed index (IntermediatePayload expectedByConstruction kind model pre mid goal) =
  BenchCase
    { caseName                 = "intermediate-random-" ++ kindName kind ++ "-seed-" ++ show seed ++ "-" ++ show index
    , caseLogic                = "intermediate"
    , caseFamily               = "random-intermediate"
    , caseMode                 = mode
    , caseExpected             = Just expectedByConstruction
    , caseStates               = basicStateCount model
    , caseActions              = length (L.actionsOf (Basic.transitions model))
    , caseTransitions          = transitionCount (Basic.transitions model)
    , casePropositions         = intermediatePropositionCount model pre mid goal
    , caseAgents               = Nothing
    , caseAutomata             = Nothing
    , caseAutomatonStates      = Nothing
    , caseAutomatonTransitions = Nothing
    , caseBudgetDim            = Nothing
    , caseFormulaSize          = intermediateFormulaSize (Intermediate.Khm pre mid goal)
    , caseRun                  = do
        salt <- freshSalt
        pure (saltOutcome salt (intermediateOutcome seed kind model pre mid goal))
    }

genIntermediatePayload :: RandomBounds -> CaseKind -> Gen IntermediatePayload
genIntermediatePayload bounds Positive =
  genIntermediatePositivePayload bounds
genIntermediatePayload bounds Negative =
  genIntermediateNegativePayload bounds

genIntermediatePositivePayload :: RandomBounds -> Gen IntermediatePayload
genIntermediatePositivePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
  preStates  <- genAtMostNonEmpty 2 prePool
  midStates  <- genAtMostNonEmpty 2 midPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, s, m) | s <- preStates, m <- midStates ]
             ++ [ (a2, m, g) | m <- midStates, g <- goalStates ])
            ([ (s, a) | s <- preStates, a <- acts ]
             ++ [ (m, a) | m <- midStates, a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, midStates)
            , (2, goalStates)
            ]
            (drop 3 props)
  pre  <- genIntermediateExactProp 0
  mid  <- genIntermediateExactProp 1
  goal <- genIntermediateExactProp 2
  pure (IntermediatePayload True Positive
    Basic.LTS
      { Basic.states      = nonEmptyStates sts
      , Basic.transitions = rels
      , Basic.valuation   = vals
      }
    pre mid goal)

genIntermediateNegativePayload :: RandomBounds -> Gen IntermediatePayload
genIntermediateNegativePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      badPre = head prePool
      badMid = head midPool
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
      preStates = [badPre]
      goodMidPool = [ s | s <- midPool ++ goalPool, s /= badMid ]
  midStates <- genAtMostNonEmpty 2 goodMidPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, badPre, badMid) ] ++ [ (a2, badMid, g) | g <- goalStates ])
            ([ (badPre, a) | a <- acts ] ++ [ (badMid, a) | a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, midStates)
            , (2, goalStates)
            ]
            (drop 3 props)
  pre  <- genIntermediateExactProp 0
  mid  <- genIntermediateExactProp 1
  goal <- genIntermediateExactProp 2
  pure (IntermediatePayload False Negative
    Basic.LTS
      { Basic.states      = nonEmptyStates sts
      , Basic.transitions = rels
      , Basic.valuation   = vals
      }
    pre mid goal)

intermediateOutcome :: Int -> CaseKind -> Basic.AbilityMap -> Intermediate.IForm -> Intermediate.IForm -> Intermediate.IForm -> BenchOutcome
intermediateOutcome seed kind model pre mid goal =
  BenchOutcome
    { outcomeResult                  = checkedResult (expectedForKind kind) semanticResult (witnessOk && witnessSize == expectedPlanWitnessSize kind)
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomeWitnessAgrees           = Just witnessAgrees
    , outcomePurpose                 = Just ("Constrained random intermediate KH " ++ kindName kind ++ " case; negatives include an ordinary path blocked by the intermediate condition.")
    , outcomePrimaryParameter        = Just "seed:kind"
    , outcomeParameterValue          = Just (show seed ++ ":" ++ kindName kind)
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (Basic.transitions model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (Basic.transitions model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedPlanWitnessSize kind
    , outcomeWitnessSizePassed       = Just (witnessSize == expectedPlanWitnessSize kind)
    }
  where
    preStates =
      Intermediate.truthSetI model pre

    midStates =
      Intermediate.truthSetI model mid

    goalStates =
      Intermediate.truthSetI model goal

    semanticResult =
      Intermediate.isTrueI (model, NE.head (Basic.states model)) (Intermediate.Khm pre mid goal)

    witness =
      Intermediate.findWitnessKhm model pre mid goal

    witnessFound =
      maybe False (const True) witness

    witnessSize =
      fmap length witness

    witnessOk =
      witnessInvariant semanticResult witness (intermediateWitnessSound model preStates midStates goalStates)

    witnessAgrees =
      witnessOk

intermediateWitnessSound :: Basic.AbilityMap -> [L.State] -> [L.State] -> [L.State] -> L.Plan -> Bool
intermediateWitnessSound model preStates midStates goalStates plan =
  all checkStart preStates
  where
    rs =
      Basic.transitions model

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

-- Regular random benchmark cases ----------------------------------------------

data RegularPayload = RegularPayload Bool CaseKind Reg.RegLTSU Reg.Agent Reg.RegForm Reg.RegForm

randomRegularBenchmarks :: BenchMode -> Int -> Int -> [BenchCase]
randomRegularBenchmarks mode baseSeed count =
  [ mkRandomRegularCase mode seed i payload
  | i <- [1 .. count]
  , let seed = seedFor baseSeed i
  , let kind = kindFor i
  , let payload = runGen (genRegularPayload (boundsFor mode) kind) seed seed
  ]

mkRandomRegularCase :: BenchMode -> Int -> Int -> RegularPayload -> BenchCase
mkRandomRegularCase mode seed index (RegularPayload expectedByConstruction kind model agent pre goal) =
  BenchCase
    { caseName                 = "regular-random-" ++ kindName kind ++ "-seed-" ++ show seed ++ "-" ++ show index
    , caseLogic                = "regular"
    , caseFamily               = "random-regular"
    , caseMode                 = mode
    , caseExpected             = Just expectedByConstruction
    , caseStates               = length (Reg.statesM model)
    , caseActions              = length (actionsOfRelations (Reg.relationsM model))
    , caseTransitions          = transitionCount (Reg.relationsM model)
    , casePropositions         = regularPropositionCount model pre goal
    , caseAgents               = Just (length (Reg.uncertainty model))
    , caseAutomata             = Just (automataCount (Reg.uncertainty model))
    , caseAutomatonStates      = Just (automatonStateCount (Reg.uncertainty model))
    , caseAutomatonTransitions = Just (automatonTransitionCount (Reg.uncertainty model))
    , caseBudgetDim            = Nothing
    , caseFormulaSize          = regularFormulaSize (Reg.KHI agent pre goal)
    , caseRun                  = do
        salt <- freshSalt
        pure (saltOutcome salt (regularOutcome seed kind model agent pre goal))
    }

genRegularPayload :: RandomBounds -> CaseKind -> Gen RegularPayload
genRegularPayload bounds Positive =
  genRegularPositivePayload bounds
genRegularPayload bounds Negative =
  genRegularNegativePayload bounds

genRegularPositivePayload :: RandomBounds -> Gen RegularPayload
genRegularPositivePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
      agent = 1
      aut = singlePlanAutomaton [a1, a2]
  preStates  <- genAtMostNonEmpty 2 prePool
  midStates  <- genAtMostNonEmpty 2 midPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, s, m) | s <- preStates, m <- midStates ]
             ++ [ (a2, m, g) | m <- midStates, g <- goalStates ])
            ([ (s, a) | s <- preStates, a <- acts ]
             ++ [ (m, a) | m <- midStates, a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  pre  <- genRegularExactProp 0
  goal <- genRegularExactProp 1
  pure (RegularPayload True Positive
    Reg.RegLTSU
      { Reg.statesM     = sts
      , Reg.relationsM  = rels
      , Reg.uncertainty = [(agent, [aut])]
      , Reg.valuationM  = vals
      }
    agent pre goal)

genRegularNegativePayload :: RandomBounds -> Gen RegularPayload
genRegularNegativePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      badPre = head prePool
      badTarget = head midPool
      a1 = head acts
      props = propsFor bounds
      agent = 1
      aut = singlePlanAutomaton [a1]
      preStates = [badPre]
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, badPre, badTarget) ]
             ++ [ (a1, badPre, g) | g <- goalStates ]
             ++ [ (a, badTarget, badTarget) | a <- acts ])
            ([ (badPre, a1) ]
             ++ [ (badTarget, a) | a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  pre  <- genRegularExactProp 0
  goal <- genRegularExactProp 1
  pure (RegularPayload False Negative
    Reg.RegLTSU
      { Reg.statesM     = sts
      , Reg.relationsM  = rels
      , Reg.uncertainty = [(agent, [aut])]
      , Reg.valuationM  = vals
      }
    agent pre goal)

regularOutcome :: Int -> CaseKind -> Reg.RegLTSU -> Reg.Agent -> Reg.RegForm -> Reg.RegForm -> BenchOutcome
regularOutcome seed kind model agent pre goal =
  BenchOutcome
    { outcomeResult                  = checkedResult (expectedForKind kind) semanticResult (witnessOk && witnessSize == expectedAutomatonWitnessSize kind)
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomeWitnessAgrees           = Just witnessAgrees
    , outcomePurpose                 = Just ("Constrained random regular KH " ++ kindName kind ++ " case with a non-empty candidate automaton language.")
    , outcomePrimaryParameter        = Just "seed:kind"
    , outcomeParameterValue          = Just (show seed ++ ":" ++ kindName kind)
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (Reg.relationsM model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (Reg.relationsM model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedAutomatonWitnessSize kind
    , outcomeWitnessSizePassed       = Just (witnessSize == expectedAutomatonWitnessSize kind)
    }
  where
    preStates =
      Reg.truthSet model pre

    goalStates =
      Reg.truthSet model goal

    semanticResult =
      Reg.isTrueReg (model, head (Reg.statesM model)) (Reg.KHI agent pre goal)

    witness =
      Reg.findWitnessAutomaton model agent pre goal

    witnessFound =
      maybe False (const True) witness

    witnessSize =
      fmap (length . autStates) witness

    witnessOk =
      witnessInvariant semanticResult witness (regularWitnessSound model pre goal)

    witnessAgrees =
      witnessOk

regularWitnessSound :: Reg.RegLTSU -> Reg.RegForm -> Reg.RegForm -> Automaton -> Bool
regularWitnessSound model pre goal aut =
  Reg.checkCond1 model aut preStates
  && Reg.checkCond2 model aut preStates negGoalStates
  where
    preStates =
      Reg.truthSet model pre

    negGoalStates =
      Reg.truthSet model (Reg.Not goal)

-- Budget random benchmark cases -----------------------------------------------

data BudgetPayload = BudgetPayload Bool CaseKind Budget.BudgetRegLTSU Budget.Budget Reg.Agent Budget.BudgetRegForm Budget.BudgetRegForm

randomBudgetBenchmarks :: BenchMode -> Int -> Int -> [BenchCase]
randomBudgetBenchmarks mode baseSeed count =
  [ mkRandomBudgetCase mode seed i payload
  | i <- [1 .. count]
  , let seed = seedFor baseSeed i
  , let kind = kindFor i
  , let payload = runGen (genBudgetPayload (boundsFor mode) kind) seed seed
  ]

mkRandomBudgetCase :: BenchMode -> Int -> Int -> BudgetPayload -> BenchCase
mkRandomBudgetCase mode seed index (BudgetPayload expectedByConstruction kind model budget agent pre goal) =
  BenchCase
    { caseName                 = "budget-random-" ++ kindName kind ++ "-seed-" ++ show seed ++ "-" ++ show index
    , caseLogic                = "budget"
    , caseFamily               = "random-budget"
    , caseMode                 = mode
    , caseExpected             = Just expectedByConstruction
    , caseStates               = length (Budget.statesBR model)
    , caseActions              = length (actionsOfRelations (Budget.relationsBR model))
    , caseTransitions          = transitionCount (Budget.relationsBR model)
    , casePropositions         = budgetPropositionCount model pre goal
    , caseAgents               = Just (length (Budget.uncertaintyBR model))
    , caseAutomata             = Just (automataCount (Budget.uncertaintyBR model))
    , caseAutomatonStates      = Just (automatonStateCount (Budget.uncertaintyBR model))
    , caseAutomatonTransitions = Just (automatonTransitionCount (Budget.uncertaintyBR model))
    , caseBudgetDim            = Just 1
    , caseFormulaSize          = budgetFormulaSize (Budget.BKHI budget agent pre goal)
    , caseRun                  = do
        salt <- freshSalt
        pure (saltOutcome salt (budgetOutcome seed kind model budget agent pre goal))
    }

genBudgetPayload :: RandomBounds -> CaseKind -> Gen BudgetPayload
genBudgetPayload bounds Positive =
  genBudgetPositivePayload bounds
genBudgetPayload bounds Negative =
  genBudgetNegativePayload bounds

genBudgetPositivePayload :: RandomBounds -> Gen BudgetPayload
genBudgetPositivePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
      agent = 1
      aut = singlePlanAutomaton [a1, a2]
      budget = 3
  preStates  <- genAtMostNonEmpty 2 prePool
  midStates  <- genAtMostNonEmpty 2 midPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, s, m) | s <- preStates, m <- midStates ]
             ++ [ (a2, m, g) | m <- midStates, g <- goalStates ])
            ([ (s, a) | s <- preStates, a <- acts ]
             ++ [ (m, a) | m <- midStates, a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  let weights = weightsWith sts acts
                  ([ ((s, a1), -1) | s <- preStates ] ++ [ ((m, a2), -1) | m <- midStates ])
  pre  <- genBudgetExactProp 0
  goal <- genBudgetExactProp 1
  pure (BudgetPayload True Positive
    Budget.BudgetRegLTSU
      { Budget.statesBR      = sts
      , Budget.relationsBR   = rels
      , Budget.uncertaintyBR = [(agent, [aut])]
      , Budget.weightsBR     = weights
      , Budget.valuationBR   = vals
      }
    budget agent pre goal)

genBudgetNegativePayload :: RandomBounds -> Gen BudgetPayload
genBudgetNegativePayload bounds = do
  (sts, acts) <- genUniverse bounds 5 2
  let (prePool, midPool, goalPool) = stateBands sts
      a1 = head acts
      a2 = acts !! 1
      props = propsFor bounds
      agent = 1
      aut = singlePlanAutomaton [a1, a2]
      budget = 1
  preStates  <- genAtMostNonEmpty 2 prePool
  midStates  <- genAtMostNonEmpty 2 midPool
  goalStates <- genAtMostNonEmpty 2 goalPool
  rels <- genRelationsWith sts acts
            ([ (a1, s, m) | s <- preStates, m <- midStates ]
             ++ [ (a2, m, g) | m <- midStates, g <- goalStates ])
            ([ (s, a) | s <- preStates, a <- acts ]
             ++ [ (m, a) | m <- midStates, a <- acts ])
  vals <- genValuationWith sts
            [ (0, preStates)
            , (1, goalStates)
            ]
            (drop 2 props)
  let weights = weightsWith sts acts
                  ([ ((s, a1), -2) | s <- preStates ] ++ [ ((m, a2), -2) | m <- midStates ])
  pre  <- genBudgetExactProp 0
  goal <- genBudgetExactProp 1
  pure (BudgetPayload False Negative
    Budget.BudgetRegLTSU
      { Budget.statesBR      = sts
      , Budget.relationsBR   = rels
      , Budget.uncertaintyBR = [(agent, [aut])]
      , Budget.weightsBR     = weights
      , Budget.valuationBR   = vals
      }
    budget agent pre goal)

budgetOutcome :: Int -> CaseKind -> Budget.BudgetRegLTSU -> Budget.Budget -> Reg.Agent -> Budget.BudgetRegForm -> Budget.BudgetRegForm -> BenchOutcome
budgetOutcome seed kind model budget agent pre goal =
  BenchOutcome
    { outcomeResult                  = checkedResult (expectedForKind kind) semanticResult (witnessOk && witnessSize == expectedAutomatonWitnessSize kind)
    , outcomeWitnessFound            = Just witnessFound
    , outcomeWitnessSize             = witnessSize
    , outcomeWitnessAgrees           = Just witnessAgrees
    , outcomePurpose                 = Just ("Constrained random budget KH " ++ kindName kind ++ " case; negatives keep regular reachability but violate budget.")
    , outcomePrimaryParameter        = Just "seed:kind"
    , outcomeParameterValue          = Just (show seed ++ ":" ++ kindName kind)
    , outcomePreStates               = Just (length preStates)
    , outcomeGoalStates              = Just (length goalStates)
    , outcomeOrdinaryReachable       = ordinaryReachable (Budget.relationsBR model) preStates goalStates
    , outcomeOrdinaryAllPreReachable = ordinaryAllPreReachable (Budget.relationsBR model) preStates goalStates
    , outcomeExpectedWitnessSize     = expectedAutomatonWitnessSize kind
    , outcomeWitnessSizePassed       = Just (witnessSize == expectedAutomatonWitnessSize kind)
    }
  where
    preStates =
      Budget.truthSetBR model pre

    goalStates =
      Budget.truthSetBR model goal

    semanticResult =
      Budget.isTrueBR (model, head (Budget.statesBR model)) (Budget.BKHI budget agent pre goal)

    witness =
      Budget.findWitnessAutomatonBR model budget agent pre goal

    witnessFound =
      maybe False (const True) witness

    witnessSize =
      fmap (length . autStates) witness

    witnessOk =
      witnessInvariant semanticResult witness (budgetWitnessSound model budget pre goal)

    witnessAgrees =
      witnessOk

budgetWitnessSound :: Budget.BudgetRegLTSU -> Budget.Budget -> Budget.BudgetRegForm -> Budget.BudgetRegForm -> Automaton -> Bool
budgetWitnessSound model budget pre goal aut =
  Reg.checkCond1 plain aut preStates
  && Reg.checkCond2 plain aut preStates negGoalStates
  && Budget.checkCond3Budget1D model aut budget preStates
  where
    plain =
      Budget.forgetBudget model

    preStates =
      Budget.truthSetBR model pre

    negGoalStates =
      Budget.truthSetBR model (Budget.BNot goal)

-- Generators -------------------------------------------------------------------

type Edge = (L.Action, L.State, L.State)
type LockedPair = (L.State, L.Action)

genUniverse :: RandomBounds -> Int -> Int -> Gen ([L.State], [L.Action])
genUniverse bounds minStates minActions = do
  n <- choose (minStates, max minStates (boundStates bounds))
  a <- choose (minActions, max minActions (boundActions bounds))
  pure ([0 .. n - 1], [1 .. a])

stateBands :: [L.State] -> ([L.State], [L.State], [L.State])
stateBands sts =
  (prePool, midPool, goalPool)
  where
    n =
      length sts

    third =
      max 1 (n `div` 3)

    prePool =
      take third sts

    midPool =
      take third (drop third sts)

    goalPool =
      drop (2 * third) sts

genAtMostNonEmpty :: Int -> [a] -> Gen [a]
genAtMostNonEmpty _ [] =
  error "genAtMostNonEmpty: empty input"
genAtMostNonEmpty maxCount xs = do
  ys <- genNonEmptySubset xs
  pure (take (max 1 maxCount) ys)

genRelationsWith :: [L.State] -> [L.Action] -> [Edge] -> [LockedPair] -> Gen L.Relations
genRelationsWith sts acts fixed locked = do
  noise <- genNoiseEdges sts acts locked
  pure (relationsFromEdges acts (fixed ++ noise))


genNoiseEdges :: [L.State] -> [L.Action] -> [LockedPair] -> Gen [Edge]
genNoiseEdges sts acts locked =
  fmap concat $ sequence
    [ genNoiseFrom s a
    | s <- sts
    , a <- acts
    ]
  where
    genNoiseFrom s a
      | (s, a) `elem` locked =
          pure []
      | otherwise = do
          include <- frequency [(3, pure False), (2, pure True)]
          if not include
             then pure []
             else do
               targets <- genNonEmptySubset sts
               pure [ (a, s, t) | t <- targets ]

relationsFromEdges :: [L.Action] -> [Edge] -> L.Relations
relationsFromEdges acts edges =
  [ (a, nub [ (s, t) | (a', s, t) <- edges, a' == a ])
  | a <- acts
  ]


genValuationWith :: [L.State] -> [(L.Proposition, [L.State])] -> [L.Proposition] -> Gen L.Valuation
genValuationWith sts controlled noiseProps =
  sequence
    [ do noise <- genSubset noiseProps
         pure (s, nub (controlledProps s ++ noise))
    | s <- sts
    ]
  where
    controlledProps s =
      [ p | (p, xs) <- controlled, s `elem` xs ]

weightsWith :: [L.State] -> [L.Action] -> [((L.State, L.Action), Budget.Cost)] -> Budget.WeightFunction
weightsWith sts acts special =
  [ ((s, a), weightFor s a)
  | s <- sts
  , a <- acts
  ]
  where
    weightFor s a =
      case lookup (s, a) special of
        Just c  -> c
        Nothing -> 0

singlePlanAutomaton :: [L.Action] -> Automaton
singlePlanAutomaton plan =
  Automaton
    { autStates      = qs
    , autAlphabet    = nub plan
    , autTransitions = [ ((q, a), [q + 1]) | (q, a) <- zip qs plan ]
    , autInitial     = [0]
    , autFinal       = [length plan]
    }
  where
    qs =
      [0 .. length plan]

genSubset :: [a] -> Gen [a]
genSubset =
  filterM (const (elements [False, True]))

genNonEmptySubset :: [a] -> Gen [a]
genNonEmptySubset [] =
  error "genNonEmptySubset: empty input"
genNonEmptySubset xs = do
  ys <- genSubset xs
  if null ys
     then pure [head xs]
     else pure ys

propsFor :: RandomBounds -> [L.Proposition]
propsFor bounds =
  [0 .. max 3 (boundProps bounds) - 1]

nonEmptyStates :: [L.State] -> NonEmpty L.State
nonEmptyStates [] =
  0 :| []
nonEmptyStates (s:ss) =
  s :| ss

genBasicExactProp :: L.Proposition -> Gen Basic.Form
genBasicExactProp p =
  frequency
    [ (4, pure (Basic.P p))
    , (2, pure (Basic.Conj Basic.T (Basic.P p)))
    , (2, pure (Basic.Neg (Basic.Neg (Basic.P p))))
    ]

genIntermediateExactProp :: L.Proposition -> Gen Intermediate.IForm
genIntermediateExactProp p =
  frequency
    [ (4, pure (Intermediate.IP p))
    , (2, pure (Intermediate.IConj Intermediate.IT (Intermediate.IP p)))
    , (2, pure (Intermediate.INeg (Intermediate.INeg (Intermediate.IP p))))
    ]

genRegularExactProp :: L.Proposition -> Gen Reg.RegForm
genRegularExactProp p =
  frequency
    [ (4, pure (Reg.Prop p))
    , (2, pure (Reg.Disj (Reg.Prop p) (Reg.Prop p)))
    , (2, pure (Reg.Not (Reg.Not (Reg.Prop p))))
    ]

genBudgetExactProp :: L.Proposition -> Gen Budget.BudgetRegForm
genBudgetExactProp p =
  frequency
    [ (4, pure (Budget.BProp p))
    , (2, pure (Budget.BDisj (Budget.BProp p) (Budget.BProp p)))
    , (2, pure (Budget.BNot (Budget.BNot (Budget.BProp p))))
    ]

-- Metrics and oracles ----------------------------------------------------------

basicStateCount :: Basic.AbilityMap -> Int
basicStateCount model =
  length (NE.toList (Basic.states model))

transitionCount :: L.Relations -> Int
transitionCount rels =
  sum [ length rel | (_, rel) <- rels ]

actionsOfRelations :: L.Relations -> [L.Action]
actionsOfRelations rels =
  nub [ a | (a, _) <- rels ]

automataCount :: Reg.Uncertainty -> Int
automataCount uncertainty =
  sum [ length auts | (_, auts) <- uncertainty ]

automatonStateCount :: Reg.Uncertainty -> Int
automatonStateCount uncertainty =
  sum [ length (autStates aut) | (_, auts) <- uncertainty, aut <- auts ]

automatonTransitionCount :: Reg.Uncertainty -> Int
automatonTransitionCount uncertainty =
  sum [ length (autTransitions aut) | (_, auts) <- uncertainty, aut <- auts ]

ordinaryReachable :: L.Relations -> [L.State] -> [L.State] -> Maybe Bool
ordinaryReachable _ [] _ =
  Nothing
ordinaryReachable _ _ [] =
  Nothing
ordinaryReachable rels preStates goalStates =
  Just (any reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates rels s)

ordinaryAllPreReachable :: L.Relations -> [L.State] -> [L.State] -> Maybe Bool
ordinaryAllPreReachable _ [] _ =
  Nothing
ordinaryAllPreReachable _ _ [] =
  Nothing
ordinaryAllPreReachable rels preStates goalStates =
  Just (all reachesGoal preStates)
  where
    reachesGoal s =
      any (`elem` goalStates) (reachableStates rels s)

reachableStates :: L.Relations -> L.State -> [L.State]
reachableStates rels start =
  go [] [start]
  where
    edges =
      nub (concatMap snd rels)

    successors s =
      [ v | (u, v) <- edges, u == s ]

    go visited [] =
      visited
    go visited (x:queue)
      | x `elem` visited =
          go visited queue
      | otherwise =
          go (x:visited) (queue ++ successors x)

basicPropositionCount :: Basic.AbilityMap -> Basic.Form -> Basic.Form -> Int
basicPropositionCount model pre goal =
  length . nub $
    concatMap snd (Basic.valuation model)
    ++ basicFormPropositions pre
    ++ basicFormPropositions goal

basicFormulaSize :: Basic.Form -> Int
basicFormulaSize Basic.T =
  1
basicFormulaSize (Basic.P _) =
  1
basicFormulaSize (Basic.Neg f) =
  1 + basicFormulaSize f
basicFormulaSize (Basic.Conj f g) =
  1 + basicFormulaSize f + basicFormulaSize g
basicFormulaSize (Basic.KH f g) =
  1 + basicFormulaSize f + basicFormulaSize g

basicFormPropositions :: Basic.Form -> [L.Proposition]
basicFormPropositions Basic.T =
  []
basicFormPropositions (Basic.P p) =
  [p]
basicFormPropositions (Basic.Neg f) =
  basicFormPropositions f
basicFormPropositions (Basic.Conj f g) =
  basicFormPropositions f ++ basicFormPropositions g
basicFormPropositions (Basic.KH f g) =
  basicFormPropositions f ++ basicFormPropositions g

intermediatePropositionCount :: Basic.AbilityMap -> Intermediate.IForm -> Intermediate.IForm -> Intermediate.IForm -> Int
intermediatePropositionCount model pre mid goal =
  length . nub $
    concatMap snd (Basic.valuation model)
    ++ intermediateFormPropositions pre
    ++ intermediateFormPropositions mid
    ++ intermediateFormPropositions goal

intermediateFormulaSize :: Intermediate.IForm -> Int
intermediateFormulaSize Intermediate.IT =
  1
intermediateFormulaSize (Intermediate.IP _) =
  1
intermediateFormulaSize (Intermediate.INeg f) =
  1 + intermediateFormulaSize f
intermediateFormulaSize (Intermediate.IConj f g) =
  1 + intermediateFormulaSize f + intermediateFormulaSize g
intermediateFormulaSize (Intermediate.Khm f g h) =
  1 + intermediateFormulaSize f + intermediateFormulaSize g + intermediateFormulaSize h

intermediateFormPropositions :: Intermediate.IForm -> [L.Proposition]
intermediateFormPropositions Intermediate.IT =
  []
intermediateFormPropositions (Intermediate.IP p) =
  [p]
intermediateFormPropositions (Intermediate.INeg f) =
  intermediateFormPropositions f
intermediateFormPropositions (Intermediate.IConj f g) =
  intermediateFormPropositions f ++ intermediateFormPropositions g
intermediateFormPropositions (Intermediate.Khm f g h) =
  intermediateFormPropositions f ++ intermediateFormPropositions g ++ intermediateFormPropositions h

regularPropositionCount :: Reg.RegLTSU -> Reg.RegForm -> Reg.RegForm -> Int
regularPropositionCount model pre goal =
  length . nub $
    concatMap snd (Reg.valuationM model)
    ++ regularFormPropositions pre
    ++ regularFormPropositions goal

regularFormulaSize :: Reg.RegForm -> Int
regularFormulaSize (Reg.Prop _) =
  1
regularFormulaSize (Reg.Not f) =
  1 + regularFormulaSize f
regularFormulaSize (Reg.Disj f g) =
  1 + regularFormulaSize f + regularFormulaSize g
regularFormulaSize (Reg.KHI _ f g) =
  1 + regularFormulaSize f + regularFormulaSize g

regularFormPropositions :: Reg.RegForm -> [L.Proposition]
regularFormPropositions (Reg.Prop p) =
  [p]
regularFormPropositions (Reg.Not f) =
  regularFormPropositions f
regularFormPropositions (Reg.Disj f g) =
  regularFormPropositions f ++ regularFormPropositions g
regularFormPropositions (Reg.KHI _ f g) =
  regularFormPropositions f ++ regularFormPropositions g

budgetPropositionCount :: Budget.BudgetRegLTSU -> Budget.BudgetRegForm -> Budget.BudgetRegForm -> Int
budgetPropositionCount model pre goal =
  length . nub $
    concatMap snd (Budget.valuationBR model)
    ++ budgetFormPropositions pre
    ++ budgetFormPropositions goal

budgetFormulaSize :: Budget.BudgetRegForm -> Int
budgetFormulaSize (Budget.BProp _) =
  1
budgetFormulaSize (Budget.BNot f) =
  1 + budgetFormulaSize f
budgetFormulaSize (Budget.BDisj f g) =
  1 + budgetFormulaSize f + budgetFormulaSize g
budgetFormulaSize (Budget.BKHI _ _ f g) =
  1 + budgetFormulaSize f + budgetFormulaSize g

budgetFormPropositions :: Budget.BudgetRegForm -> [L.Proposition]
budgetFormPropositions (Budget.BProp p) =
  [p]
budgetFormPropositions (Budget.BNot f) =
  budgetFormPropositions f
budgetFormPropositions (Budget.BDisj f g) =
  budgetFormPropositions f ++ budgetFormPropositions g
budgetFormPropositions (Budget.BKHI _ _ f g) =
  budgetFormPropositions f ++ budgetFormPropositions g
