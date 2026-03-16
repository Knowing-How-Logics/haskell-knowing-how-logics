\section{Multi Agent}\label{sec:MultiAgent}

In this section we model the language of Knowing How $reg \;L^U_{KH}$.

Given a set of proposition letters $Prop$ and a set of agents $Agt$, the language $reg \;L^U_{KH}$ is defined as 
$\varphi := p \;|\; \lnot\varphi \;|\; \varphi\land\varphi \;|\; Kh_i (\psi,\varphi) \;|\; T$ s.t. $p \in Prop$ and $i \in Agt$.

\begin{code}
module MultiAgent where

import SingleAgent

type Agent = Int

data RegForm = P Proposition | Neg RegForm | Conj RegForm RegForm | KH Agent RegForm RegForm | T
    deriving (Eq, Show, Ord)

\end{code}

Now we define automaton. 
Note that the automaton here refers to a non-deterministic automaton. 
Therefore, the transition is modeled as a relation, not a function.



An automaton is a tuple $\mathcal{A} = (Q, Act, \delta, I, F)$, where

\begin{itemize}
    \item $Q$ is a set of automaton states. In principle, this should be distinguished from the states of LTS. But in the model checking algorithm, $Q$ is equal to the set of states in LTS.
    \item $Act$ is a set of actions
    \item $\delta$ takes a state and an action, then returns a set of successor states
    \item $I$ is the singleton containing the initial state
    \item $F$ is the singleton containing the final state
\end{itemize}

Since both $I$ and $F$ are singletons we define them here as a single State, 
rather than a list, to avoid unintended behaviour. 

\begin{code}
type Successors = [State]
type ActionAtState = (State, Action) 

data Automaton = ATMN {
    states :: [State],
    actions:: [Action],
    transitions :: [(ActionAtState, Successors)],
    innitial :: State,
    final :: State
}

\end{code}