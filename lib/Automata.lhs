\hide{
\begin{code}
module Automata where

import Data.List (nub)
import Data.Maybe (fromMaybe)
\end{code}
}


\begin{code}
type AState = Int

type ASymbol = Int

data Automaton = Automaton
  { autStates      :: [AState]
  , autAlphabet    :: [ASymbol]
  , autTransitions :: [((AState, ASymbol), [AState])]
  , autInitial     :: [AState]
  , autFinal       :: [AState]
  } deriving (Eq, Show, Ord)

-- Return all successor states.
successorsA :: Automaton -> AState -> ASymbol -> [AState]
successorsA aut q a =
    fromMaybe [] (lookup (q, a) (autTransitions aut))

-- Determine whether an automaton accepts a word/plan.
accepts :: Automaton -> [ASymbol] -> Bool
accepts aut word =
    any (`elem` autFinal aut) endStates
  where
    startStates :: [AState]
    startStates = autInitial aut

    step :: [AState] -> ASymbol -> [AState]
    step qs a =
        nub [ q'
            | q <- qs
            , q' <- successorsA aut q a
            ]

    endStates :: [AState]
    endStates = foldl step startStates word

-- Return all reachable states.
reachableA :: Automaton -> [AState]
reachableA aut = go [] (autInitial aut)
  where
    go seen [] = seen
    go seen (q:queue)
        | q `elem` seen = go seen queue
        | otherwise =
            let next =
                    nub [ q'
                        | a <- autAlphabet aut
                        , q' <- successorsA aut q a
                        ]
            in go (q : seen) (queue ++ next)

-- L(A) == \emptyset?
isEmptyLanguage :: Automaton -> Bool
isEmptyLanguage aut =
    null [ q | q <- reachableA aut, q `elem` autFinal aut ]

-- L(A_1) \cap L(A_2) != \emptyset?
intersectionNonEmpty :: Automaton -> Automaton -> Bool
intersectionNonEmpty aut1 aut2 =
    go [] initialPairs
  where
    alphabet :: [ASymbol]
    alphabet = nub (autAlphabet aut1 ++ autAlphabet aut2)

    initialPairs :: [(AState, AState)]
    initialPairs =
        [ (q1, q2)
        | q1 <- autInitial aut1
        , q2 <- autInitial aut2
        ]

    isFinalPair :: (AState, AState) -> Bool
    isFinalPair (q1, q2) =
        q1 `elem` autFinal aut1 && q2 `elem` autFinal aut2

    stepPair :: (AState, AState) -> ASymbol -> [(AState, AState)]
    stepPair (q1, q2) a =
        [ (q1', q2')
        | q1' <- successorsA aut1 q1 a
        , q2' <- successorsA aut2 q2 a
        ]

    go :: [(AState, AState)] -> [(AState, AState)] -> Bool
    go _ [] = False
    go seen (p:queue)
        | p `elem` seen = go seen queue
        | isFinalPair p = True
        | otherwise =
            let next = nub [ p'
                           | a <- alphabet
                           , p' <- stepPair p a
                           ]
            in go (p : seen) (queue ++ next)

sanityCheckAutomaton :: Automaton -> Bool
sanityCheckAutomaton aut =
    not (null (autStates aut))
    && not (null (autInitial aut))
    && not (null (autFinal aut))
    && all (`elem` autStates aut) (autInitial aut)
    && all (`elem` autStates aut) (autFinal aut)
    && all validTransition (autTransitions aut)
  where
    validTransition :: ((AState, ASymbol), [AState]) -> Bool
    validTransition ((q, a), qs) =
        q `elem` autStates aut
        && a `elem` autAlphabet aut
        && all (`elem` autStates aut) qs

-- For all A_1, A_2: L(A_1) \cap L(A_2) == \emptyset?
pairwiseDisjointAutomata :: [Automaton] -> Bool
pairwiseDisjointAutomata auts =
    and [ not (intersectionNonEmpty aut1 aut2)
        | (i, aut1) <- zip [0 :: Int ..] auts
        , (j, aut2) <- zip [0 :: Int ..] auts
        , i < j
        ]
\end{code}