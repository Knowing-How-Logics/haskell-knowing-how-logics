\section{Single Agent}\label{sec:SingleAgent}

In this section we model the language of Knowing How $L_{KH}$ as by the definition of Y. Wang \cite{Wang2015}. 

Given a set of proposition letters $P$, the language $L_{KH}$ is defined as follows 
s.t. $Kh(\psi,\varphi)$ is the modality expressing "the agent knows how to achieve $\varphi$ given $\psi$". 
The abbreviations $\bot$, $\lor$, $\to$, and the universal modality $U_\varphi:=Kh(\lnot\varphi, \bot)$ have been left out for simplicity. 

\begin{code}
module SingleAgent where

import Data.List (nub, delete)
-- import NoneEmpty including its constructor :|
import Data.List.NonEmpty (NonEmpty(..), toList)
import Test.QuickCheck

type Proposition = Int

data Form = P Proposition | Neg Form | Conj Form Form | KH Form Form | T
    deriving (Eq, Show, Ord)

\end{code}

Instead of a Kripke semantics, the Logic opts for a labelled transition system (LTS) $(\mathcal{S}, \mathcal{R}, \mathcal{V})$ s.t.
$\mathcal{S}$ is a non-empty set of states, 
$\mathcal{R}:\Sigma\to 2^{\mathcal{S}\times\mathcal{S}}$ is a collection of transitions labelled by actions in $\Sigma$,
and $\mathcal{V}: \mathcal{S} \to 2^P$ is a valuation function. In the literature by Y. Wang the LTS is called an ability map. \par

When creating a LTS, consider that states :: NonEmpty State, and therefore must use the :| constructor, i.e. (n :| [n+1..]). 
For more information see NonEmpty on Hoogle.

\begin{code}
type Action = Integer
type Plan = [Action]
type State = Int
type Valuation = [(State, [Proposition])]

data AbilityMap = LTS {
    states :: NonEmpty State,
    transitions :: Relations,
    valuation :: Valuation
} deriving(Show)

\end{code}

In (Wang2015), two relational notions are introduced:

\begin{itemize}
    \item $R_a$, the atomic relation associated with an action $a$;
    \item $R_{\sigma}$, the composite relation associated with a plan $\sigma$.
\end{itemize}

Both of these are binary relations on states. Therefore, in our implementation, we use the same Haskell type \texttt{Rel} to represent them, since both can be understood as sets of pairs of states.

To represent the family of atomic relations $R = (R_a)_a$, we index relations by actions. This gives rise to the type \texttt{Relations}, corresponding to the collection of action-labelled transitions in the literature.

We do not model $R_{\sigma}$ explicitly as a separate data structure. Instead, we only implement the operations needed to reason about plan execution and strong executability.

For this purpose, we define the following helper functions:

\begin{itemize}
    \item \texttt{image}, which computes the image of a state under a relation, i.e. it collects all successor states of a given state;
    \item \texttt{r\_a}, which takes an action $a$ and the family of relations $R$, and returns the indexed relation $R_a$;
    \item \texttt{executePlan}, which computes all possible end states obtained after executing a plan from a given initial state;
    \item \texttt{stronglyExecutableAt}, which determines whether a plan is strongly executable at a given state.
\end{itemize}


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

The satisfaction relation $\models$ defines when a formula $\varphi$ is true in a given state $s$ of an ability map $\mathcal{M}$.
Before specifying the semantics, we first introduce two helper functions for the semantics of the $Kh$ operator.

\begin{code}
-- Given an LST and formula, returns the states that satify said formula
statesSatisifying :: AbilityMap -> Form -> [State]
statesSatisifying m f = [s | s <- toList (states m), isTrue (m, s) f]

-- Given an LST, find all plans.
findPlans :: AbilityMap -> [Plan]
findPlans m = nub (concatMap (plansFrom depth) (toList (states m)))
  where
    -- For now we limit the depth to avoid infinite loops.
    depth = 5

    -- Flatten transitions
    edges :: [(Action,(State,State))]
    edges = [ (a,(u,v))| (a,rel) <- transitions m, (u,v) <- rel ]

    -- Generate all plans from a given state up to our specified depth
    plansFrom :: Int -> State -> [Plan]
    plansFrom 0 _ = []
    plansFrom d s = 
        [ [a] | (a,(x,_)) <- edges, x == s ] -- single action plans
        ++ [ a:p | (a,(x,y)) <- edges, x == s, p <- plansFrom (d-1) y ]

isTrue :: (AbilityMap, State) -> Form -> Bool
isTrue _ T = True
isTrue (m, s) (P p) =
  case lookup s (valuation m) of
    Just props -> p `elem` props
    Nothing -> False
isTrue (m, s) (Neg f) = not (isTrue (m, s) f)
isTrue (m, s) (Conj f g) = isTrue (m, s) f && isTrue (m, s) g
-- KH is NOT local; its truth does not depend on the state at which it is evaluated. 
-- KH either holds at all states, or none of them. 
isTrue (m, _) (KH f g) = 
    any (\a -> 
        all (\s -> 
            stronglyExecutableAt rs s a 
            && all (\t -> isTrue (m,t) g) (executePlan rs s a)
        ) statesF
    ) candidatePlans
  where
    rs = transitions m
    statesF = statesSatisifying m f
    candidatePlans = findPlans m

-- Infix alias for the satisfaction relation
(|=) :: (AbilityMap, State) -> Form -> Bool
(|=) = isTrue
\end{code}

Finally, for this section we define the instances of Arbitrary for \texttt{Form} and \texttt{Arbitrary} respectively. 
For \texttt{Form} we use the \texttt{sized} function to ensure that the generated formulas remain finite in size.

\begin{code}
instance Arbitrary Form where
    arbitrary = sized randomForm where
        -- Helper function to generate random formulas of a given size
        randomForm :: Int -> Gen Form
        randomForm 0 = oneof [P <$> choose (1, 5), return T]
        randomForm n = oneof 
            [ P <$> choose (1, 5)
            , return T
            , Neg <$> randomForm (n - 1)
            , Conj <$> randomForm (n `div` 2) <*> randomForm (n `div` 2)
            , KH <$> randomForm (n `div` 2) <*> randomForm (n `div` 2)
            ]

instance Arbitrary AbilityMap where
    arbitrary = do
        n <- choose (1,10)
        let sts = [1..n] -- n states
        rels <- generateRelations n sts
        vals <- mapM generateValuation sts
        return $ LTS (head sts :| tail sts) rels vals 
        where
            generateRelations n sts
                | n == 1 = return []
                | otherwise = do
                    m <- choose (1,n) -- decide how many actions to generate
                    actions <- vectorOf m (choose (1,5))
                    mapM (generateRel sts) actions

             -- for each action a, generate a relation labeled by a
            generateRel sts a = do
                x <- elements sts
                y <- elements (delete x sts) -- avoid loops
                return (a, [(x,y)])
            
            -- for each state s, generate a list of propositions
            generateValuation s = do
                props <- listOf (choose (1,5))
                return (s, nub props)
        
\end{code}

For now, we haven't had time yet to implement any 'interactive' elements. But it is possible to try out semantics using the definitions by running \texttt{stack ghci}.
For example:

\begin{verbatim}
ghci> import Test.QuickCheck
ghci> import Data.List.NonEmpty (NonEmpty(..), toList)

ghci> generate (arbitrary:: Gen AbilityMap)
LTS {
    states = 1 :| [2,3,4,5,6], 
    transitions = [(3,[(5,2)]),(4,[(2,4)]),(1,[(5,4)])], 
    valuation = [(1,[4,2]),(2,[]),(3,[1]),(4,[3]),(5,[4]),(6,[])]
    }

ghci> m = ...

ghci> isTrue (m, 2::State) (KH (Conj (P 4) (Neg (P 2))) (P 3))
True

ghci> isTrue (m, 2::State) (KH (P 4) (P 1))
False
\end{verbatim}
