{- HLINT ignore "Eta reduce" -}
\section{Multi Agent}\label{sec:MultiAgent}

In this section we model the language of Uncertainty-based Knowing How with regularity constraints $reg \;L^U_{KH}$ \cite{Demri2023}. 
The paper we reference combines and alters already exisiting languages into the one we model here. 
The first key difference from the previous language being that it moves from single agent to a multi agent language. 

Given a set of proposition letters $Prop$ and a set of agents $Agt$, where $p \in Prop$ and $i \in Agt$, 
the language $reg \;L^U_{KH}$ is defined as 
$\varphi := p \;|\; \lnot\varphi \;|\; \varphi\land\varphi \;|\; Kh_i (\psi,\varphi) \;|\; T$ 
s.t. $Kh_i (\psi,\varphi)$ is the modality expressing "when $\psi$ is the case, the agent $a$ knows how to make $\varphi$ true". 

\begin{code}
module MultiAgent where
import SingleAgent
  ( Proposition
  , Action
  , Plan
  , State
  , Valuation
  , Relations
  , executePlan
  , stronglyExecutableAt
  , image
  , r_a
  )

import Data.List (nub)
import Data.Maybe (fromMaybe)

type Agent = Int

data RegForm = P Proposition | Neg RegForm | Conj RegForm RegForm | KH Agent RegForm RegForm | T
    deriving (Eq, Show, Ord)

\end{code}

Now we define the automaton used in the model-checking procedure.
This is a non-deterministic automaton of the form
\[
\mathcal{A} = (Q, Act, \delta, I, F),
\]
where, in our setting:

\begin{itemize}
    \item $Q = S$, i.e. the automaton states coincide with the states of the LTS;
    \item $Act$ is the set of actions;
    \item $\delta$ is represented as a transition relation, or equivalently as a mapping from a state-action pair to a set of successor states;
    \item $I$ is the singleton containing the initial state;
    \item $F$ is the singleton containing the final state.
\end{itemize}

Note that since the automaton here refers to a non-deterministic automaton, the transition is modeled as a relation and not a function.
Moreover, $\forall t, t'\in Q$ and $a\in Act$ we have that $t \xrightarrow{a} t' \in \delta \Leftrightarrow (t, t') \in R_a$ (as previously defined for single agent).

Since both $I$ and $F$ are singletons we define both as a \texttt{State}, 
rather than a \texttt{[State]}, to avoid unintended behaviour. 

\begin{code}
type Successors = [State]
type ActionAtState = (State, Action) 

data Automaton = ATMN {
    statesA :: [State],
    actionsA :: [Action],
    transitionsA :: [(ActionAtState, Successors)],
    initial :: State,
    final :: State
} deriving (Eq, Show, Ord)
\end{code}

\begin{code}
type PlanSet = [Plan]

-- R_pi(u) = union of R_sigma(u) for all sigma in pi
rPiU :: Relations -> State -> PlanSet -> [State]
rPiU rs u plans =
    nub (concat [executePlan rs u sigma | sigma <- plans])

-- R_pi(X) = union of R_pi(u) for all u in X
rPiX :: Relations -> [State] -> PlanSet -> [State]
rPiX rs xs plans =
    nub (concat [rPiU rs u plans | u <- xs])

-- SE(sigma) = set of all states at which sigma is strongly executable
seSigma :: [State] -> Relations -> Plan -> [State]
seSigma sts rs sigma =
    [u | u <- sts, stronglyExecutableAt rs u sigma]

-- SE(pi) = intersection of SE(sigma) for all sigma in pi
sePi :: [State] -> Relations -> PlanSet -> [State]
sePi sts rs plans =
    [u | u <- sts, all (stronglyExecutableAt rs u) plans]
\end{code}

\begin{code}
type Uncertainty = [(Agent, [Automaton])] -- U_i = {A_1,...}, for each agent i

data RegLTSU = RegLTSU{ 
        statesM :: [State],
        relationsM :: Relations,
        uncertainty :: Uncertainty,
        valuationM :: Valuation -- use the Valuation from singleAgent
    } deriving (Eq, Show, Ord)

-- TODO: Shall we write a checker to check A_i's are indeed automata. Namely, are the language of them really pairwise disjoint? Or simply leave it as an assumption?
\end{code}

\begin{code}
-- Satisfaction relation for the propositional fragment
isTrueReg :: (RegLTSU, State) -> RegForm -> Bool
isTrueReg _ T = True
isTrueReg (m, s) (P p) =
    case lookup s (valuationM m) of
        Just props -> p `elem` props
        Nothing -> False
isTrueReg (m, s) (Neg f) =
    not (isTrueReg (m, s) f)
isTrueReg (m, s) (Conj f g) =
    isTrueReg (m, s) f && isTrueReg (m, s) g
isTrueReg (_, _) (KH {}) = undefined

-- Infix alias for the satisfaction relation
(||=) :: (RegLTSU, State) -> RegForm -> Bool
(||=) = isTrueReg

-- [[phi]]= set of states that phi holds
truthSet :: RegLTSU -> RegForm -> [State]
truthSet m f = [s | s <- statesM m, isTrueReg (m, s) f]
\end{code}

Now we define the product digraph $G$ used in the model-checking procedure. 
Given a reg-LTS$^U$ $\mathcal{S}$ and an automaton $\mathcal{A} = (Q, Act, \delta, I, F)$, we construct a digraph $G = (V, E)$ as follows:

\begin{itemize}
    \item $V = Q \times S$, representing the combined state of the automaton and the underlying transition system;
    \item $E$ is the set of edges such that $((q, t), (q', t')) \in E$ if and only if there exists an action $a \in Act$ such that:
    \begin{enumerate}
        \item $q \xrightarrow{a} q'$ in $\mathcal{A}$;
        \item $(t, t') \in R_a$.
    \end{enumerate}
\end{itemize}

This construction synchronizes transitions of the automaton with transitions in the LTS under the same action, allowing us to track which runs of the automaton are realizable in the model.

\begin{code}
type GVertex = (State, State) -- (Automaton State, LTS State)
type GEdge = (GVertex, GVertex)

data Digraph = Digraph {
    vSet :: [GVertex],
    eSet :: [GEdge]
} deriving (Eq, Show, Ord)

-- Helper function to get next automaton states under a given action
getAutNext :: Automaton -> State -> Action -> [State]
getAutNext atmn q a =
    fromMaybe [] (lookup (q, a) (transitionsA atmn))

-- Helper function to get next LTS states under a given action
getLtsNext :: RegLTSU -> State -> Action -> [State]
getLtsNext m t a = image (r_a (relationsM m) a) t

-- Build the product digraph G = (V, E)
buildDigraph :: RegLTSU -> Automaton -> Digraph
buildDigraph m atmn = Digraph nodes edges
  where
    nodes = [(q, s) | q <- statesA atmn, s <- statesM m]
    edges = [ ((q, t), (q', t')) 
            | (q, t) <- nodes
            , act    <- actionsA atmn
            , q'     <- getAutNext atmn q act
            , t'     <- getLtsNext m t act
            ]
\end{code}


\begin{code}
-- Successors of a vertex in the digraph
successors :: Digraph -> GVertex -> [GVertex]
successors g v = [v' | (u, v') <- eSet g, u == v]
 
-- DFS reachability: is any vertex in targetSet reachable from start?
-- The type can be read as: digraph -> start -> targets -> visited_set -> Bool
dfsReachable :: Digraph -> GVertex -> [GVertex] -> [GVertex] -> Bool
dfsReachable _ start targetSet _
    | start `elem` targetSet = True
dfsReachable _ start _ visited
    | start `elem` visited = False
dfsReachable g start targetSet visited =
    any (\v -> dfsReachable g v targetSet (start : visited)) (successors g start)
 
-- Compute the set of bad vertices in G.
-- A vertex (q, t) is bad iff there exists an action a such that:
--   (i)  the automaton has a transition from q under a, and
--   (ii) the LTS has no successor from t under a.
badVertices :: RegLTSU -> Automaton -> [GVertex]
badVertices m atmn =
    nub [ (q, t)
        | q <- statesA atmn,
        t <- statesM m,
        a <- actionsA atmn,
        not (null (getAutNext atmn q a)),  --  delta(q,a) != empty
        null (getLtsNext m t a)            --  R_a(t) == empty
        ]
 
-- checker whether there is a path from (q0, s) to a bad vertex. 
-- If so, return True. This means that s not in SE(L(A)).
-- Else, return False. This means that s in SE(L(A)).
checkSE :: RegLTSU -> State -> Automaton -> Bool
checkSE m s atmn =
    let g     = buildDigraph m atmn -- build digraph g
        bad   = badVertices m atmn  -- compute bad vertices
        q0    = initial atmn        
        start = (q0, s)
    in  dfsReachable g start bad []

checkCond1 :: RegLTSU -> Automaton -> [State] -> Bool
checkCond1 m atmn =
    all (\s -> not (checkSE m s atmn))
\end{code}

\begin{code}
-- Construct A_(t1, t2)
-- This automaton accepts all plans from t1 to t2
buildPathAutomaton :: RegLTSU -> State -> State -> Automaton
buildPathAutomaton m t1 t2 = ATMN
    { statesA      = statesM m,
    actionsA     = acts,
    transitionsA = [ ((s, a), getLtsNext m s a) | s <- statesM m, a <- acts],
    initial      = t1,
    final        = t2
    }
  where
    -- Collect all actions that appear in the LTS relations
    acts = nub [a | (a, _) <- relationsM m]
 
-- Check the intersection of L(A1) and L(A2) is empty or not
intersectionNonEmpty :: Automaton -> Automaton -> Bool
intersectionNonEmpty a1 a2 =
    dfsReachable prodGraph startV targets []
  where
    -- Shared actions
    sharedActs = nub [a | a <- actionsA a1, a `elem` actionsA a2]
 
    -- Product graph vertices and edges
    prodNodes = [(q1, q2) | q1 <- statesA a1, q2 <- statesA a2]
    prodEdges = [ ((q1, q2), (q1', q2'))
                | (q1, q2) <- prodNodes,
                a          <- sharedActs,
                q1'        <- getAutNext a1 q1 a,
                q2'        <- getAutNext a2 q2 a
                ]
    prodGraph = Digraph prodNodes prodEdges
 
    -- Start from the pair of initial states
    startV = (initial a1, initial a2)
 
    -- Target: any pair of accepting states
    targets = [(final a1, final a2)]
 
-- Check for each A: for all (t1,t2): L(A) \cap L(A_(t1, t2)) = empty?
-- We check the emptiness of the intersection by checking the reachability of the product graph(automaton)
-- If empty, then cond 2 is SAT
checkCond2 :: RegLTSU -> Automaton -> [State] -> [State] -> Bool
checkCond2 m aut phiStates negPsiStates = not (any violates pairs)
  where
    pairs = [(t1, t2) | t1 <- phiStates, t2 <- negPsiStates]
    -- Check the intersection. Non-empty => cond 2 is UNSAT.
    violates (t1, t2) =
        let pathAut = buildPathAutomaton m t1 t2
        in  intersectionNonEmpty aut pathAut
\end{code}