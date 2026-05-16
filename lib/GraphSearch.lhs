\hide{
\begin{code}
module GraphSearch
  ( existsReachable
  , existsReachableFromAny
  , pathTo
  ) where

import qualified Data.Set as S
import qualified Data.Sequence as Seq
import Data.Sequence (Seq((:<|)), (|>))

-- Check whether a goal state is reachable from a single initial state.
existsReachable :: Ord s => (s -> Bool) -> (s -> [s]) -> s -> Bool
existsReachable isGoal next start =
    existsReachableFromAny isGoal next [start]

-- Check whether a goal state is reachable from any initial state.
existsReachableFromAny :: Ord s => (s -> Bool) -> (s -> [s]) -> [s] -> Bool
existsReachableFromAny isGoal next starts =
    go S.empty (Seq.fromList starts)
  where
    go _ Seq.Empty = False
    go visited (x :<| queue)
        | x `S.member` visited = go visited queue
        | isGoal x             = True
        | otherwise            =
            let visited' = S.insert x visited
                queue'   = foldl (|>) queue (next x)
            in go visited' queue'



--  Find a path from an initial state to a goal state.
--   The successor function returns labelled transitions:
--   each pair (a, s') means that action/label a leads to s'.
--   If a goal is reachable, the function returns the list of labels.
pathTo :: (Ord s) => (s -> Bool) -> (s -> [(a, s)]) -> s -> Maybe [a]
pathTo isGoal next start =
    go S.empty [(start, [])]
  where
    go _ [] = Nothing
    go visited ((x, path):queue)
        | x `S.member` visited = go visited queue
        | isGoal x             = Just (reverse path)
        | otherwise            =
            let visited' = S.insert x visited
                newItems =
                    [ (x', a:path)
                    | (a, x') <- next x
                    ]
            in go visited' (queue ++ newItems)
\end{code}

}

