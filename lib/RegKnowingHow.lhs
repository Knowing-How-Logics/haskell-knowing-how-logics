\section{Language Reg Knowing How}\label{sec:RegKnowingHow}

In this section we model the language of Knowing How $reg \;L^U_{KH}$.

Given a set of proposition letters $Prop$ and a set of agents $Agt$, the language $reg \;L^U_{KH}$ is defined as 
$\varphi := p \;|\; \lnot\varphi \;|\; \varphi\land\varphi \;|\; Kh_i (\psi,\varphi) \;|\; T$ s.t. $p \in Prop$ and $i \in Agt$.

\begin{code}
module RegKnowingHow where

import KnowingHow

type Agent = Int

data RegForm = P Proposition | Neg RegForm | Conj RegForm RegForm | KH Agent RegForm RegForm | T
    deriving (Eq, Show, Ord)

\end{code}