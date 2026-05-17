\section{Knowing How with Intermediate Constraints}



\begin{code}
module IntermediateKH where

import Data.List (nub, sort)
import Data.List.NonEmpty (toList)

import BasicKH
  ( AbilityMap(..)
  )

import LTS
import GraphSearch
\end{code}


\begin{code}
data IForm
    = IT
    | IP Proposition
    | INeg IForm
    | IConj IForm IForm
    | Khm IForm IForm IForm
    deriving (Eq, Show, Ord)
\end{code}

\begin{code}
truthSetI :: AbilityMap -> IForm -> [State]
truthSetI m f =
    [ s | s <- toList (states m), isTrueI (m, s) f ]

isTrueI :: (AbilityMap, State) -> IForm -> Bool
isTrueI _ IT = True
isTrueI (m, s) (IP p) =
    p `elem` valuationAt (valuation m) s
isTrueI (m, s) (INeg f) =
    not (isTrueI (m, s) f)
isTrueI (m, s) (IConj f g) =
    isTrueI (m, s) f && isTrueI (m, s) g
isTrueI (m, _) (Khm psi chi phi) =
    khmCompleteBySets m psiStates chiStates phiStates
  where
    psiStates = truthSetI m psi
    chiStates = truthSetI m chi
    phiStates = truthSetI m phi
\end{code}

\begin{code}
data ISEFlag = ISEOk | ISEBad
    deriving (Eq, Show, Ord)

type IComponent = (State, ([State], ISEFlag))
-- The first State records the original precondition state.
-- The list records the current reachable set after the current action prefix.

type IBadGoalComponent = ((State, State), [State])
-- ((t1,t2), xs) tracks states currently reachable from t1.
-- t2 is a bad goal state, i.e. a state not satisfying the goal formula.

data IProductState = IProductState
    { iHasMoved     :: Bool
    , iComponents   :: [IComponent]
    , iBadGoalComps :: [IBadGoalComponent]
    } deriving (Eq, Show, Ord)
\end{code}

\begin{code}
normaliseStatesI :: [State] -> [State]
normaliseStatesI = sort . nub

normaliseIComponent :: IComponent -> IComponent
normaliseIComponent (s, (xs, flag)) =
    (s, (normaliseStatesI xs, flag))

normaliseIBadGoalComponent :: IBadGoalComponent -> IBadGoalComponent
normaliseIBadGoalComponent (pair, xs) =
    (pair, normaliseStatesI xs)

normaliseIProductState :: IProductState -> IProductState
normaliseIProductState st =
    IProductState
        { iHasMoved =
            iHasMoved st
        , iComponents =
            map normaliseIComponent (iComponents st)
        , iBadGoalComps =
            map normaliseIBadGoalComponent (iBadGoalComps st)
        }
\end{code}

\begin{code}
hasSuccessorI :: Relations -> Action -> State -> Bool
hasSuccessorI rs a x =
    not (null (image (rA rs a) x))

allHaveSuccessorI :: Relations -> [State] -> Action -> Bool
allHaveSuccessorI rs xs a =
    all (hasSuccessorI rs a) xs

allSatisfyI :: [State] -> [State] -> Bool
allSatisfyI allowedStates = all (`elem` allowedStates)
\end{code}

\begin{code}
stepIComponent:: Relations
    -> [State]
    -> Action
    -> Bool
    -> IComponent
    -> IComponent
stepIComponent rs chiStates a hasMoved (s0, (xs, flag)) =
    case flag of
        ISEBad ->
            (s0, (xs, ISEBad))
        ISEOk ->
            let executable =
                    allHaveSuccessorI rs xs a

                maintains =
                    not hasMoved || allSatisfyI chiStates xs

                xs' =
                    stepSet rs xs a
            in if executable && maintains
               then (s0, (xs', ISEOk))
               else (s0, (xs', ISEBad))
\end{code}

\begin{code}
stepIBadGoalComponent :: Relations -> Action -> IBadGoalComponent -> IBadGoalComponent
stepIBadGoalComponent rs a (pair, xs) =
    (pair, stepSet rs xs a)
\end{code}

\begin{code}
stepIProductState
    :: Relations
    -> [State]
    -> Action
    -> IProductState
    -> IProductState
stepIProductState rs chiStates a st =
    normaliseIProductState $
        IProductState
            { iHasMoved =
                True
            , iComponents =
                map (stepIComponent rs chiStates a (iHasMoved st))
                    (iComponents st)
            , iBadGoalComps =
                map (stepIBadGoalComponent rs a)
                    (iBadGoalComps st)
            }
\end{code}

\begin{code}
initialIProductState :: [State] -> [State] -> IProductState
initialIProductState psiStates negPhiStates =
    normaliseIProductState $
        IProductState
            { iHasMoved =
                False
            , iComponents =
                [ (s, ([s], ISEOk))
                | s <- psiStates
                ]
            , iBadGoalComps =
                [ ((t1, t2), [t1])
                | t1 <- psiStates
                , t2 <- negPhiStates
                ]
            }
\end{code}

\begin{code}
acceptingIProductState :: IProductState -> Bool
acceptingIProductState st =
    all componentAccepts (iComponents st)
    && all badGoalAccepts (iBadGoalComps st)
  where
    componentAccepts :: IComponent -> Bool
    componentAccepts (_, (_, flag)) =
        flag == ISEOk

    badGoalAccepts :: IBadGoalComponent -> Bool
    badGoalAccepts ((_, badTarget), xs) =
        badTarget `notElem` xs
\end{code}

\begin{code}
khmCompleteBySets :: AbilityMap -> [State] -> [State] -> [State] -> Bool
khmCompleteBySets m psiStates chiStates phiStates =
    existsReachable acceptingIProductState next initialState
  where
    rs :: Relations
    rs =
        transitions m

    acts :: [Action]
    acts =
        actionsOf rs

    allStates :: [State]
    allStates =
        toList (states m)

    negPhiStates :: [State]
    negPhiStates =
        [ s | s <- allStates, s `notElem` phiStates ]

    initialState :: IProductState
    initialState =
        initialIProductState psiStates negPhiStates

    next :: IProductState -> [IProductState]
    next current =
        [ stepIProductState rs chiStates a current
        | a <- acts
        ]
\end{code}

\begin{code}
findWitnessKhmBySets:: AbilityMap
    -> [State]
    -> [State]
    -> [State]
    -> Maybe Plan
findWitnessKhmBySets m psiStates chiStates phiStates =
    pathTo acceptingIProductState next initialState
  where
    rs :: Relations
    rs =
        transitions m

    acts :: [Action]
    acts =
        actionsOf rs

    allStates :: [State]
    allStates =
        toList (states m)

    negPhiStates :: [State]
    negPhiStates =
        [ s | s <- allStates, s `notElem` phiStates ]

    initialState :: IProductState
    initialState =
        initialIProductState psiStates negPhiStates

    next :: IProductState -> [(Action, IProductState)]
    next current =
        [ (a, stepIProductState rs chiStates a current)
        | a <- acts
        ]
\end{code}

\begin{code}
findWitnessKhm :: AbilityMap -> IForm -> IForm -> IForm -> Maybe Plan
findWitnessKhm m psi chi phi =
    findWitnessKhmBySets m psiStates chiStates phiStates
  where
    psiStates =
        truthSetI m psi

    chiStates =
        truthSetI m chi

    phiStates =
        truthSetI m phi
\end{code}

\begin{code}
(|=~) :: (AbilityMap, State) -> IForm -> Bool
(|=~) = isTrueI
\end{code}
