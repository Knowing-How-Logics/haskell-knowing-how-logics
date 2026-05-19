module Bench.Intermediate (intermediateBenchmarks) where

import Data.List.NonEmpty (NonEmpty(..))

import qualified BasicKH as B
import qualified IntermediateKH as I
import Bench.Common

intermediateBenchmarks :: BenchMode -> [BenchCase]
intermediateBenchmarks mode =
  map (corridorCase mode) (sizes mode)
  where
    sizes Quick = [4, 6, 8, 10]
    sizes Full  = [4, 8, 12, 16, 20]

corridorCase :: BenchMode -> Int -> BenchCase
corridorCase mode n =
  BenchCase
    { caseName            = "intermediate-corridor-" ++ show n
    , caseLogic           = "intermediate"
    , caseFamily          = "corridor-safe"
    , caseMode            = mode
    , caseExpected        = Just True
    , caseStates          = n
    , caseActions         = 1
    , caseTransitions     = max 0 (n - 1)
    , casePropositions    = 3
    , caseAgents          = Nothing
    , caseAutomata        = Nothing
    , caseAutomatonStates = Nothing
    , caseBudgetDim       = Nothing
    , caseFormulaSize     = 4
    , caseRun             = pure (boolOutcome (I.isTrueI (corridorModel n, 0) formula))
    }
  where
    formula =
      I.Khm (I.IP 0) (I.IP 2) (I.IP 1)

corridorModel :: Int -> B.AbilityMap
corridorModel n =
  B.LTS
    { B.states = 0 :| [1 .. n - 1]
    , B.transitions = [(1, [(i, i + 1) | i <- [0 .. n - 2]])]
    , B.valuation = [(s, labels s) | s <- [0 .. n - 1]]
    }
  where
    labels s =
      startLabel ++ goalLabel ++ safeLabel
      where
        startLabel = [0 | s == 0]
        goalLabel  = [1 | s == n - 1]
        safeLabel  = [2 | s > 0 && s < n - 1]