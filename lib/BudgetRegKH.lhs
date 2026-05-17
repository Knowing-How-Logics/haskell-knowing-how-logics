\begin{code}
module BudgetRegKH where

import Data.List (nub)
import Data.Maybe (fromMaybe)

import LTS
import Automata
import RegKH
import GraphSearch
\end{code}

\begin{code}
type Cost = Int
type Budget = Int
type WeightFunction = [((State, Action), Cost)]
type BudgetProductVertex = (State, AState)

type Weight = [Int]
type VectorBudget = [Int]
type VectorWeightFunction = [((State, Action), Weight)]
\end{code}

\begin{code}
data BudgetRegLTSU = BudgetRegLTSU
    { statesBR      :: [State]
    , relationsBR   :: Relations
    , uncertaintyBR :: Uncertainty
    , weightsBR     :: WeightFunction
    , valuationBR   :: Valuation
    } deriving (Eq, Show, Ord)

getWeight :: BudgetRegLTSU -> State -> Action -> Cost
getWeight m s a =
    fromMaybe 0 (lookup (s, a) (weightsBR m))

forgetBudget :: BudgetRegLTSU -> RegLTSU
forgetBudget m =
    RegLTSU
        { statesM =
            statesBR m
        , relationsM =
            relationsBR m
        , uncertainty =
            uncertaintyBR m
        , valuationM =
            valuationBR m
        }
\end{code}

\begin{code}
data VectorBudgetRegLTSU = VectorBudgetRegLTSU
    { statesVBR      :: [State]
    , relationsVBR   :: Relations
    , uncertaintyVBR :: Uncertainty
    , weightsVBR     :: VectorWeightFunction
    , valuationVBR   :: Valuation
    } deriving (Eq, Show, Ord)

getVectorWeight :: VectorBudgetRegLTSU -> State -> Action -> Weight
getVectorWeight m s a =
    fromMaybe [] (lookup (s, a) (weightsVBR m))

forgetVectorBudget :: VectorBudgetRegLTSU -> RegLTSU
forgetVectorBudget m =
    RegLTSU
        { statesM =
            statesVBR m
        , relationsM =
            relationsVBR m
        , uncertainty =
            uncertaintyVBR m
        , valuationM =
            valuationVBR m
        }
\end{code}

\begin{code}
data BudgetRegForm
    = BProp Proposition
    | BNot BudgetRegForm
    | BDisj BudgetRegForm BudgetRegForm
    | BKHI Budget Agent BudgetRegForm BudgetRegForm
    deriving (Eq, Show, Ord)

data VectorBudgetRegForm
    = VBProp Proposition
    | VBNot VectorBudgetRegForm
    | VBDisj VectorBudgetRegForm VectorBudgetRegForm
    | VBKHI VectorBudget Agent VectorBudgetRegForm VectorBudgetRegForm
    deriving (Eq, Show, Ord)
\end{code}

\begin{code}
isProductiveState :: Automaton -> AState -> Bool
isProductiveState aut q =
    existsReachable (`elem` autFinal aut) next q
  where
    next :: AState -> [AState]
    next current =
        nub [ q'
            | a <- autAlphabet aut
            , q' <- successorsA aut current a
            ]

allStatesProductive :: Automaton -> Bool
allStatesProductive aut =
    all (isProductiveState aut) (autStates aut)
\end{code}

\begin{code}
lookupDistance :: BudgetProductVertex -> [(BudgetProductVertex, Cost)] -> Maybe Cost
lookupDistance =
    lookup

updateDistance :: BudgetProductVertex -> Cost -> [(BudgetProductVertex, Cost)] -> [(BudgetProductVertex, Cost)]
updateDistance v d [] =
    [(v, d)]
updateDistance v d ((u, oldD) : rest)
    | v == u =
        (u, min d oldD) : rest
    | otherwise =
        (u, oldD) : updateDistance v d rest
\end{code}

\begin{code}
budgetProductVertices :: BudgetRegLTSU -> Automaton -> [BudgetProductVertex]
budgetProductVertices m aut =
    [ (s, q)
    | s <- statesBR m
    , q <- autStates aut
    ]

budgetSuccessors :: BudgetRegLTSU -> Automaton -> BudgetProductVertex -> [(BudgetProductVertex, Cost)]
budgetSuccessors m aut (s, q) =
    [ ((s', q'), getWeight m s a)
    | a  <- autAlphabet aut
    , q' <- successorsA aut q a
    , s' <- image (rA (relationsBR m) a) s
    ]
\end{code}

\begin{code}
unsafeBudgetFrom :: BudgetRegLTSU -> Automaton -> Budget -> BudgetProductVertex -> Bool
unsafeBudgetFrom m aut budget start =
    any belowBudget finalDistances || hasRelevantNegativeCycle finalDistances
  where
    vertices :: [BudgetProductVertex]
    vertices =
        budgetProductVertices m aut

    edgeList :: [(BudgetProductVertex, BudgetProductVertex, Cost)]
    edgeList =
        [ (v, v', c)
        | v <- vertices
        , (v', c) <- budgetSuccessors m aut v
        ]

    initialDistances :: [(BudgetProductVertex, Cost)]
    initialDistances =
        [(start, 0)]

    relaxOnce :: [(BudgetProductVertex, Cost)] -> [(BudgetProductVertex, Cost)]
    relaxOnce distances =
        foldl relaxEdge distances edgeList

    relaxEdge :: [(BudgetProductVertex, Cost)] -> (BudgetProductVertex, BudgetProductVertex, Cost) -> [(BudgetProductVertex, Cost)]
    relaxEdge distances (u, v, c) =
        case lookupDistance u distances of
            Nothing ->
                distances
            Just du ->
                updateDistance v (du + c) distances

    finalDistances :: [(BudgetProductVertex, Cost)]
    finalDistances =
        iterate relaxOnce initialDistances !! length vertices

    belowBudget :: (BudgetProductVertex, Cost) -> Bool
    belowBudget (_, d) =
        budget + d < 0

    hasRelevantNegativeCycle :: [(BudgetProductVertex, Cost)] -> Bool
    hasRelevantNegativeCycle distances =
        any canStillImprove edgeList
      where
        canStillImprove (u, v, c) =
            case (lookupDistance u distances, lookupDistance v distances) of
                (Just du, Just dv) ->
                    du + c < dv
                (Just _, Nothing) ->
                    True
                _ ->
                    False
\end{code}

\begin{code}
checkCond3Budget1D :: BudgetRegLTSU -> Automaton -> Budget -> [State] -> Bool
checkCond3Budget1D m aut budget phiStates =
    allStatesProductive aut
    && not (any unsafe starts)
  where
    starts :: [BudgetProductVertex]
    starts =
        [ (s, q0)
        | s  <- phiStates
        , q0 <- autInitial aut
        ]

    unsafe :: BudgetProductVertex -> Bool
    unsafe =
        unsafeBudgetFrom m aut budget
\end{code}

\begin{code}
weightAtDimension :: Int -> Weight -> Int
weightAtDimension k w =
    if k < length w
       then w !! k
       else 0

getWeightAtDimension :: VectorBudgetRegLTSU -> Int -> State -> Action -> Cost
getWeightAtDimension m k s a =
    weightAtDimension k (getVectorWeight m s a)
\end{code}

\begin{code}
vectorBudgetProductVertices :: VectorBudgetRegLTSU -> Automaton -> [BudgetProductVertex]
vectorBudgetProductVertices m aut =
    [ (s, q)
    | s <- statesVBR m
    , q <- autStates aut
    ]

budgetSuccessorsAtDimension :: VectorBudgetRegLTSU -> Automaton -> Int -> BudgetProductVertex -> [(BudgetProductVertex, Cost)]
budgetSuccessorsAtDimension m aut k (s, q) =
    [ ((s', q'), getWeightAtDimension m k s a)
    | a  <- autAlphabet aut
    , q' <- successorsA aut q a
    , s' <- image (rA (relationsVBR m) a) s
    ]
\end{code}

\begin{code}
unsafeBudgetFromAtDimension :: VectorBudgetRegLTSU -> Automaton -> Int -> Budget -> BudgetProductVertex -> Bool
unsafeBudgetFromAtDimension m aut k budget start =
    any belowBudget finalDistances || hasRelevantNegativeCycle finalDistances
  where
    vertices :: [BudgetProductVertex]
    vertices =
        vectorBudgetProductVertices m aut

    edgeList :: [(BudgetProductVertex, BudgetProductVertex, Cost)]
    edgeList =
        [ (v, v', c)
        | v <- vertices
        , (v', c) <- budgetSuccessorsAtDimension m aut k v
        ]

    initialDistances :: [(BudgetProductVertex, Cost)]
    initialDistances =
        [(start, 0)]

    relaxOnce :: [(BudgetProductVertex, Cost)] -> [(BudgetProductVertex, Cost)]
    relaxOnce distances =
        foldl relaxEdge distances edgeList

    relaxEdge :: [(BudgetProductVertex, Cost)] -> (BudgetProductVertex, BudgetProductVertex, Cost) -> [(BudgetProductVertex, Cost)]
    relaxEdge distances (u, v, c) =
        case lookupDistance u distances of
            Nothing ->
                distances
            Just du ->
                updateDistance v (du + c) distances

    finalDistances :: [(BudgetProductVertex, Cost)]
    finalDistances =
        iterate relaxOnce initialDistances !! length vertices

    belowBudget :: (BudgetProductVertex, Cost) -> Bool
    belowBudget (_, d) =
        budget + d < 0

    hasRelevantNegativeCycle :: [(BudgetProductVertex, Cost)] -> Bool
    hasRelevantNegativeCycle distances =
        any canStillImprove edgeList
      where
        canStillImprove (u, v, c) =
            case (lookupDistance u distances, lookupDistance v distances) of
                (Just du, Just dv) ->
                    du + c < dv
                (Just _, Nothing) ->
                    True
                _ ->
                    False
\end{code}


\begin{code}
checkCond3VectorBudget :: VectorBudgetRegLTSU -> Automaton -> VectorBudget -> [State] -> Bool
checkCond3VectorBudget m aut budget phiStates =
    allStatesProductive aut
    && all dimensionSafe dimensions
  where
    dimensions :: [Int]
    dimensions =
        take (length budget) [0..]

    starts :: [BudgetProductVertex]
    starts =
        [ (s, q0)
        | s  <- phiStates
        , q0 <- autInitial aut
        ]

    dimensionSafe :: Int -> Bool
    dimensionSafe k =
        not (any (unsafeBudgetFromAtDimension m aut k (budget !! k)) starts)
\end{code}

\begin{code}
truthSetBR :: BudgetRegLTSU -> BudgetRegForm -> [State]
truthSetBR m f =
    [ s | s <- statesBR m, isTrueBR (m, s) f ]

getAgentAutsBR :: BudgetRegLTSU -> Agent -> [Automaton]
getAgentAutsBR m agent =
    fromMaybe [] (lookup agent (uncertaintyBR m))

findWitnessAutomatonBR
    :: BudgetRegLTSU
    -> Budget
    -> Agent
    -> BudgetRegForm
    -> BudgetRegForm
    -> Maybe Automaton
findWitnessAutomatonBR m budget agent phi psi =
    findFirst goodAutomaton (getAgentAutsBR m agent)
  where
    plainModel :: RegLTSU
    plainModel =
        forgetBudget m

    phiStates :: [State]
    phiStates =
        truthSetBR m phi

    negPsiStates :: [State]
    negPsiStates =
        truthSetBR m (BNot psi)

    goodAutomaton :: Automaton -> Bool
    goodAutomaton aut =
        checkCond1 plainModel aut phiStates
        && checkCond2 plainModel aut phiStates negPsiStates
        && checkCond3Budget1D m aut budget phiStates

isTrueBR :: (BudgetRegLTSU, State) -> BudgetRegForm -> Bool
isTrueBR (m, s) (BProp p) =
    p `elem` valuationAt (valuationBR m) s
isTrueBR (m, s) (BNot f) =
    not (isTrueBR (m, s) f)
isTrueBR (m, s) (BDisj f g) =
    isTrueBR (m, s) f || isTrueBR (m, s) g
isTrueBR (m, _) (BKHI budget agent phi psi) =
    case findWitnessAutomatonBR m budget agent phi psi of
        Just _ ->
            True
        Nothing ->
            False

(||=$) :: (BudgetRegLTSU, State) -> BudgetRegForm -> Bool
(||=$) = isTrueBR
\end{code}

\begin{code}
truthSetVBR :: VectorBudgetRegLTSU -> VectorBudgetRegForm -> [State]
truthSetVBR m f =
    [ s | s <- statesVBR m, isTrueVBR (m, s) f ]

getAgentAutsVBR :: VectorBudgetRegLTSU -> Agent -> [Automaton]
getAgentAutsVBR m agent =
    fromMaybe [] (lookup agent (uncertaintyVBR m))

findWitnessAutomatonVBR :: VectorBudgetRegLTSU  -> VectorBudget -> Agent -> VectorBudgetRegForm -> VectorBudgetRegForm -> Maybe Automaton
findWitnessAutomatonVBR m budget agent phi psi =
    findFirst goodAutomaton (getAgentAutsVBR m agent)
  where
    plainModel :: RegLTSU
    plainModel =
        forgetVectorBudget m

    phiStates :: [State]
    phiStates =
        truthSetVBR m phi

    negPsiStates :: [State]
    negPsiStates =
        truthSetVBR m (VBNot psi)

    goodAutomaton :: Automaton -> Bool
    goodAutomaton aut =
        checkCond1 plainModel aut phiStates
        && checkCond2 plainModel aut phiStates negPsiStates
        && checkCond3VectorBudget m aut budget phiStates

isTrueVBR :: (VectorBudgetRegLTSU, State) -> VectorBudgetRegForm -> Bool
isTrueVBR (m, s) (VBProp p) =
    p `elem` valuationAt (valuationVBR m) s
isTrueVBR (m, s) (VBNot f) =
    not (isTrueVBR (m, s) f)
isTrueVBR (m, s) (VBDisj f g) =
    isTrueVBR (m, s) f || isTrueVBR (m, s) g
isTrueVBR (m, _) (VBKHI budget agent phi psi) =
    case findWitnessAutomatonVBR m budget agent phi psi of
        Just _ ->
            True
        Nothing ->
            False

(||=*$) :: (VectorBudgetRegLTSU, State) -> VectorBudgetRegForm -> Bool
(||=*$) = isTrueVBR
\end{code}

\begin{code}
findFirst :: (a -> Bool) -> [a] -> Maybe a
findFirst _ [] =
    Nothing
findFirst predicate (x : xs)
    | predicate x =
        Just x
    | otherwise =
        findFirst predicate xs
\end{code}
