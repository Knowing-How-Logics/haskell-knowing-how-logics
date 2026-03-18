{- HLINT ignore "Eta reduce" -}
\section{Multi Agent}\label{sec:MultiAgent}

In this section we model the language of Uncertainty-based Knowing How with regularity constraints $reg-\mathcal{L}^U_{KH}$ \cite{Demri2023}. 
The paper we reference combines and alters already exisiting languages into the one we model here. 
The first key difference from the previous language being that it moves from single agent to a multi agent language. 

Given a set of proposition letters $Prop$ and a set of agents $Agt$, where $p \in Prop$ and $i \in Agt$, 
the language $reg-\mathcal{L}^U_{KH}$ is defined as 
\[
\varphi := p \;|\; \lnot\varphi \;|\; \varphi\land\varphi \;|\; Kh_i (\psi,\varphi)
\]
s.t. $Kh_i (\psi,\varphi)$ can be interpreted as "when $\psi$ is the case, the agent $a$ knows how to make $\varphi$ true". \\

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

data RegForm = P Proposition | Neg RegForm | Conj RegForm RegForm | KH Agent RegForm RegForm
    deriving (Eq, Show, Ord)

\end{code}

Now we define the automaton used in the model-checking procedure.
Formally, a non-deterministic finite automaton is a tuple $\mathcal{A} = (Q, Act, \delta, I, F)$, where:
\begin{itemize}
    \item $Q$ is a finite set of states,
    \item $Act$ is a finite alphabet of actions,
    \item $\delta \subseteq Q \times Act \times Q$ is the transition relation,
    \item $I \subseteq Q$ is the set of initial states,
    \item $F \subseteq Q$ is the set of accepting (final) states.
\end{itemize}

Note that since the automaton here refers to a non-deterministic automaton, the transition is modeled as a relation and not a function. Moreover, $\forall t, t'\in Q$ and $a\in Act$ we have that $t \xrightarrow{a} t' \in \delta \Leftrightarrow (t, t') \in R_a$ (as previously defined for single agent).\\

\begin{code}
type Successors = [State]
type ActionAtState = (State, Action) 

data Automaton = ATMN {
    statesA :: [State],
    actionsA :: [Action],
    transitionsA :: [(ActionAtState, Successors)],
    initial :: [State],
    final :: [State]
} deriving (Eq, Show, Ord)
\end{code}

For $\pi\subseteq Act^{*}$, $u\in W$ and $U\subseteq W$, define:
\[R_{\pi} \,:=\,\bigcup_{\sigma\in \pi}R_{\sigma}, \qquad R_{\pi}(u) \,:=\,\bigcup_{\sigma\in \pi}R_{\sigma}(u), \qquad R_{\pi}(U) \,:=\,\bigcup_{u\in U}R_{\pi}(u)\]
A set of plans $\pi\subseteq Act^{*}$ is \textit{strongly executable} at $u\in W$ iff every plan $\sigma \in \pi$ is strongly executable at $u$. This gives rise to the definition $SE(\pi)\, :=\,\bigcap_{\sigma\in\pi}SE(\sigma)$, collecting all states where every plan in $\pi$ is strongly executable.\\

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

The functions above are not used directly in the model-checking algorithm, but are included to align with the notions from the paper.\par

Each agent has sets of indistinguishable plans, forming equivalence classes. Since plans are finite sequences of actions, they can be viewed as strings over $Act$. From this perspective, each equivalence class can be represented as the language of a finite automaton $\mathcal{A}$, and a witness for $Kh_i$ is a string in $L(\mathcal{A})$.\par

A reg-LTS$^U$ is a tuple $\mathcal{M}=(W, (R_a)_{a\in Act}, (U_i)_{i\in Agt}, V)$, where the elements of $U_i$ associated to an agent $i$, are \textit{finite automata}, namely, $\emptyset \not = U_i = \{\mathcal{A}_1, \mathcal{A}_2...\}$. $L(\mathcal{A}_i)$ denotes the language accepted by $\mathcal{A}_i$. For every $\mathcal{A}_m, \mathcal{A}_n\in U_i$, s.t. $m\not = n$, then  $L(\mathcal{A}_m)\cap L(\mathcal{A}_n)=\emptyset$.\\

\begin{code}
type Uncertainty = [(Agent, [Automaton])] -- U_i = {A_1,...}, for each agent i

data RegLTSU = RegLTSU{ 
        statesM :: [State],
        relationsM :: Relations,
        uncertainty :: Uncertainty,
        valuationM :: Valuation -- use the Valuation from singleAgent
    } deriving (Eq, Show, Ord)

-- Given an agent i, return U_i = [A_1,...]
getAgentAuts :: RegLTSU -> Agent -> [Automaton]
getAgentAuts m agent =
    fromMaybe [] (lookup agent (uncertainty m))

-- TODO: Shall we write a checker to check A_i's are indeed automata. Namely, are the language of them really pairwise disjoint? Or simply leave it as an assumption?
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

This construction synchronizes transitions of the automaton with transitions in the LTS under the same action, allowing us to track which runs of the automaton are realizable in the model.\\

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
    let g   = buildDigraph m atmn
        bad = badVertices m atmn
    in  any (\q0 -> dfsReachable g (q0, s) bad []) (initial atmn)

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
    initial      = [t1],
    final        = [t2]
    }
  where
    -- Collect all actions that appear in the LTS relations
    acts = nub [a | (a, _) <- relationsM m]
 
-- Check the intersection of L(A1) and L(A2) is empty or not
intersectionNonEmpty :: Automaton -> Automaton -> Bool
intersectionNonEmpty a1 a2 =
    any (\sv -> dfsReachable prodGraph sv targets []) startVs
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

    -- Start from any pair of initial states
    startVs = [(q1, q2) | q1 <- initial a1, q2 <- initial a2]

    -- Target: any pair of accepting states
    targets = [(q1, q2) | q1 <- final a1, q2 <- final a2]
 
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

\begin{code}
-- [[phi]]= set of states that phi holds
truthSet :: RegLTSU -> RegForm -> [State]
truthSet m f = [s | s <- statesM m, isTrueReg (m, s) f]

-- Satisfaction relation for the propositional fragment
isTrueReg :: (RegLTSU, State) -> RegForm -> Bool
isTrueReg (m, s) (P p) =
    case lookup s (valuationM m) of
        Just props -> p `elem` props
        Nothing -> False
isTrueReg (m, s) (Neg f) =
    not (isTrueReg (m, s) f)
isTrueReg (m, s) (Conj f g) =
    isTrueReg (m, s) f && isTrueReg (m, s) g

-- Kh_a(phi, psi) holds iff there exists A in U_a such that
-- (1) [[phi]] is subset of SE(L(A))      
-- (2) R_{L(A)}([[phi]]) is subset of [[psi]]  
isTrueReg (m, _) (KH agent phi psi) =
    any (\aut -> checkCond1 m aut phiStates
              && checkCond2 m aut phiStates negPsiStates
    ) (getAgentAuts m agent)
  where
    phiStates    = truthSet m phi          -- [[phi]]
    negPsiStates = truthSet m (Neg psi)    -- [[neg psi]]

-- Infix alias for the satisfaction relation
(||=) :: (RegLTSU, State) -> RegForm -> Bool
(||=) = isTrueReg
\end{code}