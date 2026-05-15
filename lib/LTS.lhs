\begin{code}
module LTS
  ( State
  , Action
  , Proposition
  , Plan
  , Rel
  , Relations
  , Valuation
  , image
  , rA
  , executePlan
  , stronglyExecutableAt
  , actionsOf
  , stepSet
  , valuationAt
  ) where

import Data.List (nub)
import Data.Maybe (fromMaybe)

type State = Int
type Action = Int
type Proposition = Int
type Plan = [Action]

type Rel = [(State, State)]
type Relations = [(Action, Rel)]
type Valuation = [(State, [Proposition])]

-- Image of a state under a binary relation
image :: Rel -> State -> [State]
image r u =
  [ v | (x, v) <- r, x == u ]

-- Given a family of action-indexed relations and an action a,
-- return the corresponding relation R_a
rA :: Relations -> Action -> Rel
rA rs a =
  fromMaybe [] (lookup a rs)

-- Execute a plan from a state.
-- This computes R_sigma(u).
executePlan :: Relations -> State -> Plan -> [State]
executePlan _  u []       = [u]
executePlan rs u (a:sigma) =
  nub
    [ t
    | v <- image (rA rs a) u
    , t <- executePlan rs v sigma
    ]

-- A plan is strongly executable at a state if every possible
-- partial execution can be continued by the next action.
stronglyExecutableAt :: Relations -> State -> Plan -> Bool
stronglyExecutableAt _  _ [] = True
stronglyExecutableAt rs u (a:sigma) =
  let next = image (rA rs a) u
  in not (null next)
     && all (\v -> stronglyExecutableAt rs v sigma) next

-- Extract the action alphabet from a family of relations
actionsOf :: Relations -> [Action]
actionsOf rs =
  nub [ a | (a, _) <- rs ]

-- Compute R_a(X) for a set/list of states X
stepSet :: Relations -> [State] -> Action -> [State]
stepSet rs xs a =
  nub
    [ y
    | x <- xs
    , y <- image (rA rs a) x
    ]

-- Read the valuation of a state
valuationAt :: Valuation -> State -> [Proposition]
valuationAt val s =
  fromMaybe [] (lookup s val)
\end{code}