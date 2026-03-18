{- HLINT ignore "Eta reduce" -}
\section{Multi Agent}\label{sec:MultiAgent}

In this section we model the language of Uncertainty-based Knowing How with regularity constraints $reg-\mathcal{L}^U_{KH}$ \cite{Demri2023}. 
The paper we reference combines and alters already existing languages into the one we model here. 
The first key difference from the previous language is that it moves from a single-agent language to a multi-agent one. 

Given a set of proposition letters $Prop$ and a set of agents $Agt$, where $p \in Prop$ and $i \in Agt$, 
the language $reg-\mathcal{L}^U_{KH}$ is defined as 
\[
\varphi := p \;|\; \lnot\varphi \;|\; \varphi\lor\varphi \;|\; Kh_i (\psi,\varphi)
\]
s.t. $Kh_i (\psi,\varphi)$ can be interpreted as "when $\psi$ is the case, the agent $i$ knows how to make $\varphi$ true".\par
The semantics of this language is defined as follows.
Let $\mathcal{S} = (S, (R_a)_{a \in Act}, (U_i)_{i \in Agt}, V)$ be a finite reg-LTS$^U$, and $s \in S$. The satisfaction relation $\models$ is defined as:

\begin{tabularx}{\textwidth}{lclX} 
$\mathcal{S}, s \models p$ & \textit{iff} & & $p \in V(s)$ \\
$\mathcal{S}, s \models \neg \varphi$ & \textit{iff} & & $\mathcal{S}, s \not\models \varphi$ \\
$\mathcal{S}, w \models \psi \vee \varphi$ & \textit{iff} & & $\mathcal{S}, w \models \psi \text{ or } \mathcal{S}, w \models \varphi$ \\
$\mathcal{S}, s \models Kh_i(\psi, \varphi)$ & \textit{iff} & & there is a finite automaton $\mathcal{A}\in U_i$, such that (1) $[\![\psi]\!]^{\mathcal{S}}\subseteq SE(L(\mathcal{A}))$ and (2) for every $t\in [\![\psi]\!]^\mathcal{S}$, $R_{L(\mathcal{A})}(t) \subseteq [\![\varphi]\!]^\mathcal{S}$,\\
\end{tabularx}
where $[\![\psi]\!]^{\mathcal{S}} := \{w\in S \mid \mathcal{S}, w \models \psi\}$ is the set of all states satisfying $\psi$.
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

data RegForm = P Proposition | Neg RegForm | Disj RegForm RegForm | KH Agent RegForm RegForm
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

Since the automaton considered here is non-deterministic, its transition component is modeled as a relation rather than as a function. 
For the special automaton $\mathcal{A}_{(t_1,t_2)}$ used later in Condition (2), we define its transitions by mirroring the LTS relations: for all $t,t' \in Q$ and $a \in Act$,
\[
t \xrightarrow{a} t' \in \delta \iff (t,t') \in R_a.
\]
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

In terms of automata, $\mathrm{SE}(L(\mathcal{A})) := \bigcap_{\sigma \in L(\mathcal{A})} \mathrm{SE}(\sigma)$ collects all states at which every plan in $L(\mathcal{A})$ is strongly executable, and $R_{L(\mathcal{A})} := \bigcup_{\sigma \in L(\mathcal{A})} R_{\sigma}$ collects all transitions realisable by some plan in $L(\mathcal{A})$. The functions above are not used directly in the model-checking algorithm, but are included to align with the notions from the paper.\par

Each agent has sets of indistinguishable plans, forming equivalence classes. Since plans are finite sequences of actions, they can be viewed as strings over $Act$. From this perspective, each equivalence class can be represented as the language of a finite automaton $\mathcal{A}$, and a witness for $Kh_i$ is a string in $L(\mathcal{A})$.\par

A reg-LTS$^U$ is a tuple $\mathcal{S}=(S, (R_a)_{a\in Act}, (U_i)_{i\in Agt}, V)$, where the elements of $U_i$ associated with an agent $i$ are \textit{finite automata}, namely, $\emptyset \neq U_i = \{\mathcal{A}_1, \mathcal{A}_2, \ldots\}$. Here, $L(\mathcal{A}_i)$ denotes the language accepted by $\mathcal{A}_i$. For every $\mathcal{A}_m, \mathcal{A}_n \in U_i$ such that $m \neq n$, we have $L(\mathcal{A}_m)\cap L(\mathcal{A}_n)=\emptyset$.\\

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
    \item $V = Q \times S$, representing the combined states of the automaton and the underlying transition system;
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

Given a finite reg-LTS$^U$ $\mathcal{S} = (S, (R_a)_{a \in Act}, (U_i)_{i \in Agt}, V)$, 
a state $s \in S$, and a formula $Kh_a(\varphi, \psi)$, 
we check whether $\mathcal{S}, s \models Kh_a(\varphi, \psi)$ by iterating over 
all automata $\mathcal{A} \in U_a$ and verifying two conditions:
\begin{enumerate}
    \item $\llbracket\varphi\rrbracket^{\mathcal{S}} \subseteq \mathrm{SE}(L(\mathcal{A}))$
    \item $R_{L(\mathcal{A})}(\llbracket\varphi\rrbracket^{\mathcal{S}}) \subseteq \llbracket\psi\rrbracket^{\mathcal{S}}$
\end{enumerate}
where $\llbracket\varphi\rrbracket^{\mathcal{S}}$ is the set of states in $\mathcal{S}$ at which $\varphi$ holds.
Since $L(\mathcal{A})$ may be infinite, directly enumerating all plans is not feasible. 
Following \cite{Demri2023}, we handle each condition via a separate algorithm, 
both of which reduce the problem to reachability checks on finite graphs.\par
To perform the reachability checks in PTIME, we use the following \textit{depth-first search} algorithm:\\
{\small
\begin{algorithmic}[1]
\Require Digraph $G=(V,E)$, start vertex $v_0$, target set $T_0 \subseteq V$
\State $v \gets v_0$
\State $T \gets T_0$
\State $visited \gets \emptyset$
\Function{DFS}{$G, v, T, visited$}
    \If{$v \in T$} \Return \textbf{true} \EndIf
    \If{$v \in visited$} \Return \textbf{false} \EndIf
    \State $visited \gets visited \cup \{v\}$
    \For{$w \in \mathrm{successors}(G, v)$}
        \If{\Call{DFS}{$G, w, T, visited$}} \Return \textbf{true} \EndIf
    \EndFor
    \State \Return \textbf{false}
\EndFunction
\end{algorithmic}
}
In Haskell:\\
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
\end{code}

The algorithm that checks Condition (1) from \cite{Demri2023} works as follows:
{\small
\begin{algorithmic}[1]
\Require reg-LTS$^U$ $\mathcal{S}$, state $s \in S$, automaton $\mathcal{A} = (Q, Act, \delta, I, F)$
\Function{CheckSE-Original}{$\mathcal{S}, s, \mathcal{A}$}
    \State Build the product digraph $G = (Q \times S,\; E)$
    \For{$a \in Act$}
        \For{$t \in S$ such that $R_a(t) = \emptyset$}
            \For{$q \in Q$ such that $\delta(q, a) \neq \emptyset$}
                \For{$q_0 \in I$}
                    \If{$(q, t)$ is reachable from $(q_0, s)$ in $G$}
                        \State \Return \textbf{true}
                    \EndIf
                \EndFor
            \EndFor
        \EndFor
    \EndFor
    \State \Return \textbf{false}
\EndFunction
\end{algorithmic}
}
Instead of using the nested for-loops, we first collect all \emph{bad vertices} via set comprehension, i.e.\ 
\[
Bad = \{(q,t) \in Q \times S \mid \exists\, a \in Act : \delta(q,a) \neq \emptyset \;\text{and}\; R_a(t) = \emptyset\},
\]
and then perform a single DFS reachability check from each initial vertex $(q_0, s)$ to the set $Bad$. This is equivalent to the original procedure, but avoids repeated reachability checks.\par
A bad vertex $(q, t)$ represents a situation where the automaton expects to perform some action $a$ at state $q$, but the LTS cannot execute $a$ at state $t$. If such a vertex is reachable, it means that some plan in $L(\mathcal{A})$ fails to be strongly executable.\par
\textit{Remark: This function might be more accurately called \texttt{checkNotSE} rather than \texttt{checkSE}, since it returns true exactly when strong executability fails.}\\
{\small
\begin{algorithmic}[1]
\Require reg-LTS$^U$ $\mathcal{S} = (S, (R_a), (U_i), V)$, state $s \in S$, automaton $\mathcal{A} = (Q, Act, \delta, I, F)$
\Function{CheckSE}{$\mathcal{S}, s, \mathcal{A}$}
    \State Build product digraph $G = (Q \times S,\; E)$
    \State $Bad \gets \{(q,t) \in V \mid \exists\, a \in Act : \delta(q,a) \neq \emptyset \;\text{and}\; R_a(t) = \emptyset\}$
    \For{$q_0 \in I$}
        \If{\Call{DFS}{$(q_0, s)$} with target $Bad$} \Return \textbf{true} \EndIf
    \EndFor
    \State \Return \textbf{false}
\EndFunction
\end{algorithmic}
}

{\small
\begin{algorithmic}[1]
\Require reg-LTS$^U$ $\mathcal{S}$, automaton $\mathcal{A}$, truth set $\llbracket\varphi\rrbracket^{\mathcal{S}}$
\Function{CheckCond1}{$\mathcal{S}, \mathcal{A}, \llbracket\varphi\rrbracket^{\mathcal{S}}$}
    \For{$s \in \llbracket\varphi\rrbracket^{\mathcal{S}}$}
        \If{\Call{CheckSE}{$\mathcal{S}, s, \mathcal{A}$}} \Return \textbf{false} \EndIf
    \EndFor
    \State \Return \textbf{true}
\EndFunction
\end{algorithmic}
}
In Haskell:\\
\begin{code}
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
isTrueReg (m, s) (Disj f g) =
    isTrueReg (m, s) f || isTrueReg (m, s) g

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