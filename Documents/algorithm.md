# Algorithm of Reachability 
In both conditions of the model checking, we need to check the reachability of a digraph given two points.

Since it was proven that the model checking problem for this logic is PTIME, we should ensure the algorithm we use is also in PTIME. Thus, we can try DFS/BFS. Since we are using Haskell, I think DFS looks easier to implement.

Here is a DFS algorithm for checking reachability:
```
Driver(G, start, target):
    visited := []
    return DFS_Reachability(G, start, targetSet, visited)

DFS_Reachability(G, start, targetSet, visited):
    if start in targetSet:
        return True

    visited.push(start)
    
    for v in successor(start):
        if v not in visited:
            if DFS_Reachability(G, v, targetSet, visited):
                return True
            
    return False

```