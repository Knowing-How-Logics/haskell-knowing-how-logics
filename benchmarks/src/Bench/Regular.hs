module Bench.Regular (regularBenchmarks) where

import qualified RegKH as R
import Automata
import Bench.Common

regularBenchmarks :: BenchMode -> [BenchCase]
regularBenchmarks mode =
  map (regularLineCase mode) (sizes mode)
  where
    sizes Quick = [4, 6, 8, 10]
    sizes Full  = [4, 8, 12, 16, 20]

regularLineCase :: BenchMode -> Int -> BenchCase
regularLineCase mode n =
  BenchCase
    { caseName            = "regular-line-" ++ show n
    , caseLogic           = "regular"
    , caseFamily          = "line-automata"
    , caseMode            = mode
    , caseExpected        = Just True
    , caseStates          = n
    , caseActions         = 1
    , caseTransitions     = max 0 (n - 1)
    , casePropositions    = 2
    , caseAgents          = Just 1
    , caseAutomata        = Just 1
    , caseAutomatonStates = Just n
    , caseBudgetDim       = Nothing
    , caseFormulaSize     = 3
    , caseRun             = pure (boolOutcome (R.isTrueReg (regularModel n, 0) formula))
    }
  where
    formula =
      R.KHI 1 (R.Prop 0) (R.Prop 1)

regularModel :: Int -> R.RegLTSU
regularModel n =
  R.RegLTSU
    { R.statesM     = [0 .. n - 1]
    , R.relationsM  = [(1, [(i, i + 1) | i <- [0 .. n - 2]])]
    , R.uncertainty = [(1, [lineAutomaton n])]
    , R.valuationM  = [(s, labels s) | s <- [0 .. n - 1]]
    }
  where
    labels s =
      startLabel ++ goalLabel
      where
        startLabel = [0 | s == 0]
        goalLabel  = [1 | s == n - 1]

lineAutomaton :: Int -> Automaton
lineAutomaton n =
  Automaton
    { autStates      = [0 .. n - 1]
    , autAlphabet    = [1]
    , autTransitions = [((i, 1), [i + 1]) | i <- [0 .. n - 2]]
    , autInitial     = [0]
    , autFinal       = [n - 1]
    }