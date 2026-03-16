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

type Agent = Int

data RegForm = P Proposition | Neg RegForm | Conj RegForm RegForm | KH Agent RegForm RegForm | T
    deriving (Eq, Show, Ord)

\end{code}

Now we define \texttt{Automaton}, which we will later use in our new extended version of \texttt{LTS}. 
An automaton is a tuple $\mathcal{A} = (Q, Act, \delta, I, F)$, where

\begin{itemize}
    \item $Q$ is a set of automaton states. In principle, this should be distinguished from the states of LTS. But in the model checking algorithm, $Q$ is equal to the set of states in LTS.
    \item $Act$ is a set of actions, previously descriped as $\Sigma$
    \item $\delta$ takes a state and an action, then returns a set of successor states
    \item $I$ is the singleton containing the initial state
    \item $F$ is the singleton containing the final state
\end{itemize}

Note that since the automaton here refers to a non-deterministic automaton, the transition is modeled as a relation and not a function.
Moreover, $\forall t, t'\in Q$ and $a\in Act$ we have that $t \xrightarrow{a} t' \in \delta \Leftrightarrow (t, t') \in R_a$ (as previously defined for single agent).

Since both $I$ and $F$ are singletons we define both as a \texttt{State}, 
rather than a \texttt{[State]}, to avoid unintended behaviour. 

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