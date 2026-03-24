\section{Uncertainty-based Knowing-how logic with Regularity Constraints $reg\text{-}\mathcal{L}^U_{KH}$}\label{sec:MultiAgent}

In the framework of \textit{basic knowing how} we introduced above, an agent possesses the ability to achieve the goal $\varphi$ given $\psi$ if and only if he has a plan that is fail-proof, meaning that each partial execution must be completable. In scenarios where the agent lacks this ability, it is only because a sequence of actions cannot be generated due to certain environmental constraints. However, another scenario may also occur: the agent does not know which plan is adequate for the situation. All he can do is blindly apply a plan he thought might work, which may or may not be successful. Such \textit{indistinguishability} among plans establishes an epistemic relation of \textit{knowing that}.\par

We now introduce a new logic of \textit{knowing how} for a multi-agent setting defined in \cite{Demri2023}, extending the LTS with a notion of epistemic indistinguishability between plans. The uncertainty of an agent is encoded by equivalence classes of plans, and each such class is represented by a finite automaton. More precisely, each equivalence class of indistinguishable plans is represented by the language recognised by a finite automaton.\par

In Theorem 2 from \cite{Demri2023}, it is shown that the model-checking problem for this logic is in PTIME. The proof relies on reducing both conditions of the $Kh_i$-modality to graph reachability checks. In this section, we provide a concrete implementation of this algorithm in Haskell, closely following the constructions from the paper.\par


\subsection{Preliminaries}

\begin{definition}[Syntax]
Given a set of proposition letters $Prop$ and a set of agents $Agt$, where $p \in Prop$ and $i \in Agt$, the language $reg\text{-}\mathcal{L}^U_{KH}$ is defined by
\[
\varphi := p \;|\; \lnot\varphi \;|\; \varphi\lor\varphi \;|\; Kh_i(\psi,\varphi).
\]
\end{definition}

We first introduce the automata used to represent classes of plans.

\begin{definition}[Automaton]
A non-deterministic finite automaton is a tuple $\mathcal{A} = (Q, Act, \delta, I, F)$, where:
\begin{itemize}
    \item $Q$ is a finite set of states,
    \item $Act$ is a finite alphabet of actions,
    \item $\delta : Q \times Act \to 2^Q$ is a transition function,
    \item $I \subseteq Q$ is the set of initial states,
    \item $F \subseteq Q$ is the set of accepting (final) states.
\end{itemize}
\end{definition}

To connect an automaton with the underlying transition system, we use the following product digraph.

\begin{definition}[Digraph]
Given a reg-LTS$^U$ $\mathcal{S}$ and an automaton $\mathcal{A} = (Q, Act, \delta, I, F)$, we define a digraph $G = (V, E)$ as follows:
\begin{itemize}
    \item $V = Q \times S$, representing the combined states of the automaton and the underlying transition system;
    \item $E$ is the set of edges such that $((q, t), (q', t')) \in E$ if and only if there exists an action $a \in Act$ such that:
    \begin{enumerate}
        \item $q \xrightarrow{a} q'$ in $\mathcal{A}$;
        \item $(t, t') \in R_a$.
    \end{enumerate}
\end{itemize}
\end{definition}

This construction synchronizes transitions of the automaton with transitions of the LTS under the same action, allowing us to track which runs of the automaton are realizable in the model.

We next recall the relational notions needed for the semantics.

\begin{definition}
For $\pi\subseteq Act^{*}$, $u\in S$, and $U\subseteq S$, define
\[
R_{\pi} \,:=\,\bigcup_{\sigma\in \pi}R_{\sigma}, \qquad
R_{\pi}(u) \,:=\,\bigcup_{\sigma\in \pi}R_{\sigma}(u), \qquad
R_{\pi}(U) \,:=\,\bigcup_{u\in U}R_{\pi}(u).
\]
A set of plans $\pi\subseteq Act^{*}$ is \textit{strongly executable} at $u\in S$ iff every plan $\sigma \in \pi$ is strongly executable at $u$. This gives rise to the definition $SE(\pi)\, :=\,\bigcap_{\sigma\in\pi}SE(\sigma)$,
which collects all states at which every plan in $\pi$ is strongly executable.
\end{definition}

These notions can be lifted from plan sets to automata via their accepted languages.

\begin{definition}
In terms of automata, $\mathrm{SE}(L(\mathcal{A})) := \bigcap_{\sigma \in L(\mathcal{A})} \mathrm{SE}(\sigma)$ collects all states at which every plan in $L(\mathcal{A})$ is strongly executable, and $R_{L(\mathcal{A})} := \bigcup_{\sigma \in L(\mathcal{A})} R_{\sigma}$ collects all transitions realisable by some plan in $L(\mathcal{A})$.
\end{definition}

We now define reg-LTS$^U$ models.

\begin{definition}
A reg-LTS$^U$ is a tuple $\mathcal{S}=(S, (R_a)_{a\in Act}, (U_i)_{i\in Agt}, V)$, where the elements of $U_i$ associated with an agent $i$ are finite automata, namely,
\[
\emptyset \neq U_i = \{\mathcal{A}_1, \mathcal{A}_2, \ldots\}.
\]
Here, $L(\mathcal{A}_i)$ denotes the language accepted by $\mathcal{A}_i$. Moreover, for every $\mathcal{A}_m, \mathcal{A}_n \in U_i$ such that $m \neq n$, we have
\[
L(\mathcal{A}_m)\cap L(\mathcal{A}_n)=\emptyset.
\]
\end{definition}

Finally, we can state the semantics of the language.

\begin{definition}[Semantics]
Let $\mathcal{S} = (S, (R_a)_{a \in Act}, (U_i)_{i \in Agt}, V)$ be a finite reg-LTS$^U$, and $s \in S$. The satisfaction relation $\models$ is defined as:

\begin{tabularx}{\textwidth}{lclX} 
$\mathcal{S}, s \Vdash p$ & \textit{iff} & & $p \in V(s)$ \\
$\mathcal{S}, s \Vdash \neg \varphi$ & \textit{iff} & & $\mathcal{S}, s \not\Vdash \varphi$ \\
$\mathcal{S}, s \Vdash \psi \vee \varphi$ & \textit{iff} & & $\mathcal{S}, s \Vdash \psi \text{ or } \mathcal{S}, s \Vdash \varphi$ \\
$\mathcal{S}, s \Vdash Kh_i(\psi, \varphi)$ & \textit{iff} & & there is a finite automaton $\mathcal{A}\in U_i$, such that (1) $[\![\psi]\!]^{\mathcal{S}}\subseteq SE(L(\mathcal{A}))$ and (2) for every $t\in [\![\psi]\!]^\mathcal{S}$, $R_{L(\mathcal{A})}(t) \subseteq [\![\varphi]\!]^\mathcal{S}$,\\
\end{tabularx}
where $[\![\psi]\!]^{\mathcal{S}} := \{w\in S \mid \mathcal{S}, s \Vdash \psi\}$ is the set of all states satisfying $\psi$. 
\end{definition}
The $Kh_i (\psi,\varphi)$ can be interpreted as "when $\psi$ is the case, the agent $i$ knows how to make $\varphi$ true". $Kh_i $ is also a global modality.
\subsection{Haskell Representation}
The syntax is modelled following Definition~4.1.\\
\begin{code}
module MultiAgent where

import SingleAgent
  ( Proposition
  , Action
  , Plan
  , State
  , Valuation
  , Rel
  , Relations
  , executePlan
  , stronglyExecutableAt
  , image
  , r_a
  )

import Data.List (nub)
import Data.Maybe (fromMaybe)
import Test.QuickCheck

-- import parsec but hide State to avoid conflicts
import Text.Parsec hiding (State)

type Agent = Int

data RegForm = Prop Proposition | Not RegForm | Disj RegForm RegForm | KHI Agent RegForm RegForm
    deriving (Eq, Show, Ord)

\end{code}

The automaton type implements Definition~4.2.\\

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

The product digraph from Definition~4.3 is implemented below. The helper functions \texttt{getAutNext} and \texttt{getLtsNext} retrieve successor states in the automaton and LTS respectively.\\
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

The following functions implement the relational notions from Definition~4.4.\\
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

The functions above are not used directly in the model-checking algorithm, but are included to align with the notions from the paper. For the same reason, we omit the implementation of definition~4.5. Because 4.4 and 4.5 are simply same concepts but in different perspectives.\par

Finally, the reg-LTS$^U$ model implements Definition~4.6.\\
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
\end{code}

\subsection{Model checker in Haskell}
We now discuss the implementation model checking algorithms for $reg\text{-}\mathcal{L}^U_{KH}$ in Haskell.\par
Given a finite reg-LTS$^U$ $\mathcal{S} = (S, (R_a)_{a \in Act}, (U_i)_{i \in Agt}, V)$, 
a state $s \in S$, and a formula $Kh_i(\varphi, \psi)$, we check whether $\mathcal{S}, s \models Kh_i(\varphi, \psi)$ by iterating over 
all automata $\mathcal{A} \in U_a$ and verifying two conditions:
\begin{enumerate}
    \item $\llbracket\varphi\rrbracket^{\mathcal{S}} \subseteq \mathrm{SE}(L(\mathcal{A}))$
    \item $R_{L(\mathcal{A})}(\llbracket\varphi\rrbracket^{\mathcal{S}}) \subseteq \llbracket\psi\rrbracket^{\mathcal{S}}$
\end{enumerate}
Once we find such automaton, the formula $Kh_i(\varphi, \psi)$ is then satisfied.
Since $L(\mathcal{A})$ may be infinite, directly enumerating all plans is not feasible. 
Following \cite{Demri2023}, we handle each condition via a separate algorithm, 
both of which reduce the problem to reachability checks on finite graphs.\par
To perform the reachability checks in PTIME, we use the following \textit{depth-first search} algorithm:\\
{\small
\begin{algorithmic}[1]
\Require Digraph $G=(V,E)$, start vertex $v_0$, target set $T_0 \subseteq V$
\State \Call{DFS}{$G, v_0, T_0, \emptyset$}

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
The algorithm above runs in $O(|V|+|E|)$, which is polynomial.
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

Let $\mathcal{A}_1$ and $\mathcal{A}_2$ be two automata. To check whether $L(\mathcal{A}_1)\cap L(\mathcal{A}_2) \neq \emptyset$, it suffices to construct the product automaton and check whether any accepting state pair in $F_1 \times F_2$ is reachable from some initial state pair in $I_1 \times I_2$.\\
{\small
\begin{algorithmic}[1]
\Require Automata $\mathcal{A}_1 = (Q_1, Act_1, \delta_1, I_1, F_1)$ and $\mathcal{A}_2 = (Q_2, Act_2, \delta_2, I_2, F_2)$
\Function{IntersectionNonEmpty}{$\mathcal{A}_1, \mathcal{A}_2$}\\
    //Build product automaton
    \State $V \gets Q_1 \times Q_2$
    \State $E \gets \{((q_1,q_2),(q_1',q_2')) \mid a \in Act_1 \cap Act_2,\; q_1 \xrightarrow{a} q_1' \in \delta_1,\; q_2 \xrightarrow{a} q_2' \in \delta_2\}$
    \State $G \gets (V, E)$
    \State $T \gets F_1 \times F_2$
    \For{$(q_1, q_2) \in I_1 \times I_2$}
        \If{\Call{DFS}{$(q_1, q_2)$} with target $T$} \Return \textbf{true} \EndIf
    \EndFor
    \State \Return \textbf{false}
\EndFunction
\end{algorithmic}
}
To check Condition (2), it suffices to check whether
\[
L(\mathcal{A})\cap \bigcup \{L(\mathcal{A}_{(t_1,t_2)})\mid t_1 \in \llbracket\varphi\rrbracket^{\mathcal{S}},\, t_2 \in \llbracket\neg\psi\rrbracket^{\mathcal{S}}\}=\emptyset,
\]
where $\mathcal{A}_{(t_1,t_2)} = (S, Act, \delta', \{t_1\}, \{t_2\})$ is the path automaton whose transitions mirror the LTS, i.e.\ $\delta'(t, a) = \{t' \mid (t, t') \in R_a\}$. Its language is precisely $L(\mathcal{A}_{(t_1,t_2)}) = \{\sigma \in Act^* \mid t_2 \in R_\sigma(t_1)\}$.

By distributivity of $\cap$ over $\bigcup$, this is equivalent to checking that
\[
L(\mathcal{A})\cap L(\mathcal{A}_{(t_1,t_2)})=\emptyset \quad \text{for all } (t_1, t_2) \in \llbracket\varphi\rrbracket^{\mathcal{S}} \times \llbracket\neg\psi\rrbracket^{\mathcal{S}}.
\]

{\small
\begin{algorithmic}[1]
\Require reg-LTS$^U$ $\mathcal{S}$, automaton $\mathcal{A}$, truth sets $\llbracket\varphi\rrbracket^{\mathcal{S}}$ and $\llbracket\neg\psi\rrbracket^{\mathcal{S}}$
\Function{CheckCond2}{$\mathcal{S}, \mathcal{A}, \llbracket\varphi\rrbracket^{\mathcal{S}}, \llbracket\neg\psi\rrbracket^{\mathcal{S}}$}
    \For{$t_1 \in \llbracket\varphi\rrbracket^{\mathcal{S}}$}
        \For{$t_2 \in \llbracket\neg\psi\rrbracket^{\mathcal{S}}$}
            \If{\Call{IntersectionNonEmpty}{$\mathcal{A}, \mathcal{A}_{(t_1,t_2)}$}} \Return \textbf{false} \EndIf
        \EndFor
    \EndFor
    \State \Return \textbf{true}
\EndFunction
\end{algorithmic}
}

In Haskell:\\

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
Following the semantics defined in Definition~4.7 and putting things together, we complete the model checker for $reg\text{-}\mathcal{L}^U_{KH}$.\\
\begin{code}
-- [[phi]]= set of states that phi holds
truthSet :: RegLTSU -> RegForm -> [State]
truthSet m f = [s | s <- statesM m, isTrueReg (m, s) f]

-- Satisfaction relation for the propositional fragment
isTrueReg :: (RegLTSU, State) -> RegForm -> Bool
isTrueReg (m, s) (Prop p) =
    case lookup s (valuationM m) of
        Just props -> p `elem` props
        Nothing -> False
isTrueReg (m, s) (Not f) =
    not (isTrueReg (m, s) f)
isTrueReg (m, s) (Disj f g) =
    isTrueReg (m, s) f || isTrueReg (m, s) g

-- Kh_a(phi, psi) holds iff there exists A in U_a such that
-- (1) [[phi]] is subset of SE(L(A))      
-- (2) R_{L(A)}([[phi]]) is subset of [[psi]]  
isTrueReg (m, _) (KHI agent phi psi) =
    any (\aut -> checkCond1 m aut phiStates
              && checkCond2 m aut phiStates negPsiStates
    ) (getAgentAuts m agent)
  where
    phiStates    = truthSet m phi          -- [[phi]]
    negPsiStates = truthSet m (Not psi)    -- [[neg psi]]

-- Infix alias for the satisfaction relation
(||=) :: (RegLTSU, State) -> RegForm -> Bool
(||=) = isTrueReg
\end{code}

\subsection{Parsing for $reg\text{-}\mathcal{L}^U_{KH}$}
Formulas may be created in \texttt{ghci} using \texttt{parseForm}. The following inputs are accepted.
\begin{itemize}
    \item \texttt{p} or \texttt{P} followed by an integer \(n\) returns \texttt{P n}
    \item \texttt{!} followed by a valid input \(p\) returns \texttt{Neg p}
    \item \texttt{v} or \texttt{V} prefixed to valid inputs \(p\) and \(q\) returns \texttt{Disj p q}
    \item \texttt{KH} followed by an index \(i\) and valid inputs \(p\) and \(q\) returns \texttt{KH i p q}
    \item \texttt{->} prefixed to valid inputs \(p\) and \(q\) returns \texttt{Disj (Not p) q} (abbreviation)
    \item \texttt{\^{}} prefixed to valid inputs \(p\) and \(q\) returns \texttt{Not (Disj (Not p) (Not q))} (abbreviation)
\end{itemize}

\begin{code}
pRegForm :: Parsec String () RegForm
pRegForm = spaces *> pImpl where
    -- Start parsing at implication level
    -- Abbreviation: Implication (right-associative)
    pImpl = chainr1 pDisj (spaces *> string "->" *> spaces >> return (Disj . Not))
    
    -- Disjunction (left-associative)
    pDisj = chainl1 pConj (spaces *> oneOf "vV" *> spaces >> return Disj)
    
    -- Abbreviation: Conjunction (left-associative)
    pConj = chainl1 pPrefix (spaces *> char '^' *> spaces >> return (\p q -> Not (Disj (Not p) (Not q))))

    pPrefix = try pNeg 
        <|> try pKH 
        <|> pRemainder 
    
    -- Negation
    pNeg = char '!' >> spaces >> Not <$> pPrefix

    -- Knowing How for Agent
    pKH = KHI <$> (string "KH" >> spaces *> pAgent) 
        <*> (spaces *> pPrefix) 
        <*> (spaces *> pPrefix)
    pAgent = read <$> many1 digit
    
    pRemainder = pVar <|> between (char '(' *> spaces) (spaces *> char ')') pRegForm
    pVar = spaces *> oneOf "pP" *> spaces *> (Prop . read <$> many1 digit) <* spaces
    
    

parseRegForm :: String -> Either ParseError RegForm
parseRegForm = parse (pRegForm <* eof) "input"

evalRegForm :: (RegLTSU, State) -> String -> Bool
evalRegForm (m, s) str =
    case parseRegForm str of
        Right f -> isTrueReg (m, s) f
        Left _  -> error "Invalid formula"

\end{code}

\subsection{Random Generation for $reg\text{-}\mathcal{L}^U_{KH}$}

\subsubsection{Model Generation with Parameters}

To facilitate testing in the multi-agent setting, we provide a function that generates a random reg-LTS$^U$ model with a fixed number of states, propositions, actions, and agents. 

The generated model includes:
\begin{itemize}
    \item a finite set of states $\{1,\dots,n\}$,
    \item a set of actions $\{1,\dots,k\}$,
    \item a valuation assigning each state a random subset of propositions $\{1,\dots,m\}$,
    \item a family of action-labelled transitions,
    \item and for each agent, a set of automata representing uncertainty over plans.
\end{itemize}

\begin{code}
-- Generate a random reg-LTS^U model with parameters
-- n: number of states
-- m: number of propositions
-- k: number of actions
-- a: number of agents
generateRegLTSU :: Int -> Int -> Int -> Int -> Gen RegLTSU
generateRegLTSU n m k numAgents = do
    let n' = max 1 n
    let m' = max 0 m
    let k' = max 0 k
    let a' = max 1 numAgents

    let sts = [1 .. n']
    let acts = [1 .. fromIntegral k']
    let props = [1 .. m']

    -- Generate transitions
    rels <- mapM (\_ -> generateRandomRel sts) acts

    -- Generate valuations
    vals <- mapM (generateRandomValuation props) sts

    -- Generate uncertainty (automata per agent)
    auts <- mapM (\_ -> generateAutomata sts acts) [1 .. a']

    return $ RegLTSU sts (zip acts rels) (zip [1..] auts) vals


-- Generate a random relation (same style as single-agent)
generateRandomRel :: [State] -> Gen Rel
generateRandomRel sts = do
    numEdges <- choose (0, length sts * length sts)
    edges <- vectorOf numEdges $ do
        u <- elements sts
        v <- elements sts
        return (u, v)
    return (nub edges)


-- Generate valuation for a state
generateRandomValuation :: [Proposition] -> State -> Gen (State, [Proposition])
generateRandomValuation props s = do
    ps <- sublistOf props
    return (s, ps)


-- Generate a list of automata for one agent
generateAutomata :: [State] -> [Action] -> Gen [Automaton]
generateAutomata sts acts = do
    numAuts <- choose (1, 3)
    vectorOf numAuts (generateAutomaton sts acts)


-- Generate a simple random automaton
generateAutomaton :: [State] -> [Action] -> Gen Automaton
generateAutomaton sts acts = do
    let qs = sts

    trans <- sequence
        [ do next <- sublistOf qs
             return ((q, a), next)
        | q <- qs, a <- acts
        ]

    initStates <- sublistOf qs
    finalStates <- sublistOf qs

    return $ ATMN
        { statesA = qs
        , actionsA = acts
        , transitionsA = trans
        , initial = if null initStates then [head qs] else initStates
        , final = if null finalStates then [head qs] else finalStates
        }
\end{code}

It is possible to generate models and test formulas interactively in \texttt{ghci}. For instance:

\begin{verbatim}
ghci> m <- generate (generateRegLTSU 5 3 2 2)
ghci> m
RegLTSU {statesM = [1,2,3,4,5], 
relationsM = [(1,[(1,1),(3,1),(4,2)]),
(2,[(4,4),(5,4),(1,1),(1,2),(3,2),
(1,3),(4,3),(5,3),(1,4),(5,1),(3,1),
(2,3),(2,1),(1,5),(2,4),(4,2)])], 
uncertainty = [(1,[ATMN {statesA = [1,2,3,4,5], actionsA = [1,2], 
transitionsA = [((1,1),[2,3]),((1,2),[1,3,5]),((2,1),[1,3,5]),
((2,2),[1,2,3]),((3,1),[2,4]),((3,2),[3,4]),
((4,1),[1,3]),((4,2),[2,4,5]),((5,1),[4]),((5,2),[3])], 
initial = [3], final = [3,5]}]),
(2,[ATMN {statesA = [1,2,3,4,5], actionsA = [1,2], 
transitionsA = [((1,1),[3,5]),
((1,2),[1,2,5]),((2,1),[1,3,5]),((2,2),[1,3,4,5]),
((3,1),[2,5]),((3,2),[5]),((4,1),[1,3]),
((4,2),[3,4,5]),((5,1),[3]),((5,2),[3])], 
initial = [2,5], final = [1,3,5]}])], 
valuationM = [(1,[1,3]),(2,[1,3]),(3,[1]),(4,[1,2,3]),(5,[1,3])]}

-- Evaluate a formula at a state
ghci> isTrueReg (m, 1) (KHI 1 (Prop 1) (Prop 2))
False

-- Using the parser
ghci> evalRegForm (m, 1) "KH1 p1 p2"
False
\end{verbatim}

In the example above, \texttt{generateRegLTSU 5 3 2 2} produces a model with five states, three propositions, two actions, and two agents. Each agent is associated with a randomly generated set of automata representing its uncertainty over plans.

\subsubsection{Arbitrary Instances for QuickCheck}

To support property-based testing, we define generators for both formulas and models in the multi-agent setting.

Since the structure of formulas is independent of any particular model, the generator is defined separately from model generation. However, to avoid mismatches between formulas and models, we parameterize the generator by the number of agents. This ensures that all occurrences of the modality $Kh_i$ refer only to valid agent indices.\\

\begin{code}
-- Generate a random RegForm with bounded size and a fixed number of agents
generateRegForm :: Int -> Int -> Gen RegForm
generateRegForm numAgents = randomRegForm
  where
    numAgents' = max 1 numAgents

    randomRegForm :: Int -> Gen RegForm
    randomRegForm 0 = Prop <$> choose (1, 5)
    randomRegForm n = oneof
        [ Prop <$> choose (1, 5)
        , Not <$> randomRegForm (n - 1)
        , Disj <$> randomRegForm (n `div` 2) <*> randomRegForm (n `div` 2)
        , KHI <$> choose (1, numAgents')
              <*> randomRegForm (n `div` 2)
              <*> randomRegForm (n `div` 2)
        ]
\end{code}
