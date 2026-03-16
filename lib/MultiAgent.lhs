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