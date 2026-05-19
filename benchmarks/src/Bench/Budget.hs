module Bench.Budget (budgetBenchmarks) where

import qualified BudgetRegKH as B
import Automata
import Bench.Common
import RegKH (Uncertainty)

budgetBenchmarks :: BenchMode -> [BenchCase]
budgetBenchmarks mode =
  oneDimensional ++ vectorDimensional
  where
    sizes Quick = [4, 6, 8, 10]
    sizes Full  = [4, 8, 12, 16, 20]

    oneDimensional =
      map (budget1DCase mode) (sizes mode)

    vectorDimensional =
      map (vectorBudgetCase mode) (sizes mode)

budget1DCase :: BenchMode -> Int -> BenchCase
budget1DCase mode n =
  BenchCase
    { caseName            = "budget-1d-line-" ++ show n
    , caseLogic           = "budget"
    , caseFamily          = "one-dimensional"
    , caseMode            = mode
    , caseExpected        = Just True
    , caseStates          = n
    , caseActions         = 1
    , caseTransitions     = max 0 (n - 1)
    , casePropositions    = 2
    , caseAgents          = Just 1
    , caseAutomata        = Just 1
    , caseAutomatonStates = Just n
    , caseBudgetDim       = Just 1
    , caseFormulaSize     = 3
    , caseRun             = pure (boolOutcome (B.isTrueBR (budgetModel n, 0) formula))
    }
  where
    formula =
      B.BKHI (n - 1) 1 (B.BProp 0) (B.BProp 1)

vectorBudgetCase :: BenchMode -> Int -> BenchCase
vectorBudgetCase mode n =
  BenchCase
    { caseName            = "budget-vector-line-" ++ show n
    , caseLogic           = "budget"
    , caseFamily          = "vector"
    , caseMode            = mode
    , caseExpected        = Just True
    , caseStates          = n
    , caseActions         = 1
    , caseTransitions     = max 0 (n - 1)
    , casePropositions    = 2
    , caseAgents          = Just 1
    , caseAutomata        = Just 1
    , caseAutomatonStates = Just n
    , caseBudgetDim       = Just 2
    , caseFormulaSize     = 3
    , caseRun             = pure (boolOutcome (B.isTrueVBR (vectorBudgetModel n, 0) formula))
    }
  where
    formula =
      B.VBKHI [n - 1, n - 1] 1 (B.VBProp 0) (B.VBProp 1)

budgetModel :: Int -> B.BudgetRegLTSU
budgetModel n =
  B.BudgetRegLTSU
    { B.statesBR      = [0 .. n - 1]
    , B.relationsBR   = relations n
    , B.uncertaintyBR = uncertainty n
    , B.weightsBR     = [((i, 1), -1) | i <- [0 .. n - 2]]
    , B.valuationBR   = valuation n
    }

vectorBudgetModel :: Int -> B.VectorBudgetRegLTSU
vectorBudgetModel n =
  B.VectorBudgetRegLTSU
    { B.statesVBR      = [0 .. n - 1]
    , B.relationsVBR   = relations n
    , B.uncertaintyVBR = uncertainty n
    , B.weightsVBR     = [((i, 1), [-1, -1]) | i <- [0 .. n - 2]]
    , B.valuationVBR   = valuation n
    }

relations :: Int -> [(Int, [(Int, Int)])]
relations n =
  [(1, [(i, i + 1) | i <- [0 .. n - 2]])]

valuation :: Int -> [(Int, [Int])]
valuation n =
  [(s, labels s) | s <- [0 .. n - 1]]
  where
    labels s =
      startLabel ++ goalLabel
      where
        startLabel = [0 | s == 0]
        goalLabel  = [1 | s == n - 1]

uncertainty :: Int -> Uncertainty
uncertainty n =
  [(1, [lineAutomaton n])]

lineAutomaton :: Int -> Automaton
lineAutomaton n =
  Automaton
    { autStates      = [0 .. n - 1]
    , autAlphabet    = [1]
    , autTransitions = [((i, 1), [i + 1]) | i <- [0 .. n - 2]]
    , autInitial     = [0]
    , autFinal       = [n - 1]
    }