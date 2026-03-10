\section{Language Knowing How}\label{sec:KnowingHow}

Given a set of proposition letters $P$, we define the language $L_{KH}$ as follows 
s.t. $Kh(\psi,\varphi)$ is the modality expressing "the agent knows how to achieve $\varphi$ given $\psi$":

\begin{code}
module KnowingHow where

type Proposition = Integer

data Form = P Proposition | Neg Form | Conj Form Form | KH Form Form | T
    deriving (Eq, Show, Ord)


type Action = Integer

type Plan = [Action]

type State = Integer

-- Both R_a and R_sigma share the same type
type Rel = [(State, State)]



\end{code}