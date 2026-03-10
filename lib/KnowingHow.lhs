\section{Language Knowing How}\label{sec:KnowingHow}

In this section we model the language of Knowing How $L_{KH}$ as by the definition of Y. Wang (2015). 

Given a set of proposition letters $P$, the language $L_{KH}$ is defined as follows 
s.t. $Kh(\psi,\varphi)$ is the modality expressing "the agent knows how to achieve $\varphi$ given $\psi$". 
The abbreviations $\bot$, $\lor$, $\to$, and the universal modality $U_\varphi:=Kh(\lnot\varphi, \bot)$ have been left out for simplicity.

\begin{code}
module KnowingHow where

import Data.List (nub)
import Data.List.NonEmpty (NonEmpty)

type Proposition = Integer

data Form = P Proposition | Neg Form | Conj Form Form | KH Form Form | T
    deriving (Eq, Show, Ord)

\end{code}

Instead of a Kripke semantics, the Logic opts for a labelled transition system (LTS) $(\mathcal{S}, \mathcal{R}, \mathcal{V})$ s.t.
$\mathcal{S}$ is a non-empty set of states, 
$\mathcal{R}:\Sigma\to 2^{\mathcal{S}\times\mathcal{S}}$ is a collection of transitions labelled by actions in $\Sigma$,
and $\mathcal{V}: \mathcal{S} \to 2^P$ is a valuation function. In the literature by Y. Wang the LTS is called an ability map.

\begin{code}
type Action = Integer
type Plan = [Action]
type State = Integer
type Valuation = [(State, [Proposition])]

data AbilityMap = LTS {
    states :: NonEmpty State, -- NonEmpty must use the :| constructor, i.e. (n :| [n+1..])
    transitions :: Relations,
    valuation :: Valuation
}

\end{code}

TODO: comments about rel, relations, image, etc. (what they do, what they represent from the literature)

\begin{code}
-- Both $R_a$ and $R_\sigma$ share the same type. 
-- Here we model the whole set of relations, without classification.
type Rel = [(State, State)]

-- The family of action-indexed relations (R_a)_a
type Relations = [(Action, Rel)]

-- Image of a state under R_a
image :: Rel -> State -> [State]
image r u = [v | (x, v) <- r, x == u]

-- Given (R_a)_a and an action x, return R_x
r_a :: Relations -> Action -> Rel
r_a rs a =
    case lookup a rs of
        Just r  -> r
        Nothing -> []

-- Execute a plan from a given start state
-- This corresponds to R_sigma(u)
executePlan :: Relations -> State -> Plan -> [State]
executePlan _  u []       = [u]
executePlan rs u (a:sigma) =
    nub (concat [ executePlan rs v sigma | v <- image (r_a rs a) u ])

-- Plan is SE or not at a state
stronglyExecutableAt :: Relations -> State -> Plan -> Bool
stronglyExecutableAt _  _ []       = True
stronglyExecutableAt rs u (a:sigma) =
    let next = image (r_a rs a) u
    in  not (null next) &&
        all (\v -> stronglyExecutableAt rs v sigma) next
\end{code}