\hide{
\begin{code}
module GraphSearch
  ( existsReachable
  , existsReachableFromAny
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
\end{code}
}

