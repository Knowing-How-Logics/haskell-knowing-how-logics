\section{Basic Knowing How Logic $\mathcal{L}_{Kh}$}\label{sec:SingleAgent}
In this section we model the language of $\mathcal{L}_{Kh}$ introduced in \cite{Wang2015}. This captures the basic idea of an agent knowing how to achieve a goal under certain condition. We implement an explicit model-checker for this logic with a bounded plan depth, along with \texttt{QuickCheck} generators for random testing of the semantics.
\subsection{Preliminaries}
\begin{definition}(Syntax)
Given a set of proposition letters $Prop$, the language $\mathcal{L}_{Kh}$ is defined by
\[
\varphi\, ::= \top\mid \, p\,|\, \neg \varphi\,|\, \varphi\wedge\varphi \, | \,Kh(\varphi,\varphi), 
\]
where $p \in Prop$.
\end{definition}

\begin{definition}[LTS]
A \textit{labelled transition system} (LTS) is a tuple $\mathcal{M} = (S, (R_a)_{a \in Act}, V)$, where:
\begin{itemize}
    \item $S$ is a non-empty set of \textit{states},
    \item $(R_a)_{a \in Act}$ is a family of \textit{binary relations} on $S$, each labelled by an \textit{action} $a \in Act$,
    \item $V: S \to 2^{Prop}$ is a \textit{valuation function}.
\end{itemize}

We write $s \xrightarrow{a} t$ if $(s,t) \in R_a$. For a plan $\sigma = a_1 \ldots a_n \in Act^*$, we write $s \xrightarrow{\sigma} t$ if there exist $s_1, \ldots, s_{n-1}$ such that $s \xrightarrow{a_1} s_1 \xrightarrow{a_2} \cdots \xrightarrow{a_n} t$. A plan $\sigma = a_1 \ldots a_n$ is \textit{strongly executable} at $s$ iff for every $0 \leq k < n$ and every $t$ such that $s \xrightarrow{\sigma_k} t$, the state $t$ has at least one $a_{k+1}$-successor.
\end{definition}

\begin{definition}[Semantics]
Let $\mathcal{M} $ be an LTS, and $s$ be a state.

\begin{tabularx}{\textwidth}{lclX}
$\mathcal{M}, s \models \top$ & \textit{iff}& & \textit{always} \\
$\mathcal{M}, s \models p$ & \textit{iff} & & $p \in V(s)$ \\
$\mathcal{M}, s \models \neg\varphi$ & \textit{iff} & & $\mathcal{M}, s \not\models \varphi$ \\
$\mathcal{M}, s \models \varphi \land \psi$ & \textit{iff} & & $\mathcal{M}, s \models \varphi$ and $\mathcal{M}, s \models \psi$ \\
$\mathcal{M}, s \models Kh(\psi, \varphi)$ & \textit{iff} & & there exists a $\sigma \in Act^*$ such that for all $s'$ such that $\mathcal{M}, s' \models \psi$: \\
& & & $\sigma$ is strongly executable at $s'$ and for all $t$ such that $s' \xrightarrow{\sigma} t$, $\mathcal{M}, t \models \varphi$ \\
\end{tabularx}
\end{definition}

The $Kh(\psi,\varphi)$ can be interpreted as "the agent knows how to achieve $\varphi$ given $\psi$". Notice that the $Kh$ is a global modality. Namely, either it holds for all states, or none of them.

\subsection{Haskell Representation}
The syntax is modelled following Definition~2.1. By using the $\mathsf{PSPACE}$-algorithm from \cite{Demri2023}.\\

\hide{
\begin{code}
module BasicKH where

import Data.List (nub, delete, sort)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Text.Parsec hiding (State)
import Test.QuickCheck
import LTS
import GraphSearch
\end{code}
}

\begin{code}
data Form = P Proposition | Neg Form | Conj Form Form | KH Form Form | T
    deriving (Eq, Show, Ord)

\end{code}

\hide{

Following Definition~2.2, we model the LTS as follows.
When creating a LTS, consider that states is a non-empty list and therefore must use the :| constructor, i.e. (n :| [n+1..]). \\

\begin{code}
data AbilityMap = LTS {
    states :: NonEmpty State,
    transitions :: Relations,
    valuation :: Valuation
} deriving(Show)

\end{code}

\begin{code}
-- Given an LTS and formula, returns the states that satisfy said formula
statesSatisifyingBounded :: AbilityMap -> Form -> [State]
statesSatisifyingBounded m f =
    [s | s <- toList (states m), isTrueBounded (m, s) f]

-- Given an LTS, find all plans.
findPlans :: AbilityMap -> [Plan]
findPlans m = [] : nub (concatMap (plansFrom depth) (toList (states m)))
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


\end{code}


\begin{code}
isTrueBounded :: (AbilityMap, State) -> Form -> Bool
isTrueBounded _ T = True
isTrueBounded (m, s) (P p) =
  p `elem` valuationAt (valuation m) s
isTrueBounded (m, s) (Neg f) = not (isTrueBounded (m, s) f)
isTrueBounded (m, s) (Conj f g) = isTrueBounded (m, s) f && isTrueBounded (m, s) g

-- KH is NOT local; its truth does not depend on the state at which it is evaluated. 
-- KH either holds at all states, or none of them. 
isTrueBounded (m, _) (KH f g) = 
    any (\a -> 
        all (\s -> 
            stronglyExecutableAt rs s a 
            && all (\t -> isTrueBounded (m,t) g) (executePlan rs s a)
        ) statesF
    ) candidatePlans
  where
    rs = transitions m
    statesF = statesSatisifyingBounded m f
    candidatePlans = findPlans m

\end{code}
}



\begin{code}
data SEFlag = SEOk | SEBad
    deriving (Eq, Show, Ord)

type SEComponent = (State, ([State], SEFlag))
-- The first State records the original precondition state.
-- The list records the current set of states reachable after the current action prefix.

type BadPairComponent = ((State, State), [State])
-- ((t1,t2), xs) tracks states currently reachable from t1.
-- t2 is a bad target, i.e. a state not satisfying the goal formula.

data KHProductState = KHProductState
    { seComponentsKH  :: [SEComponent]
    , badComponentsKH :: [BadPairComponent]
    } deriving (Eq, Show, Ord)

normaliseStates :: [State] -> [State]
normaliseStates = sort . nub

normaliseSEComponent :: SEComponent -> SEComponent
normaliseSEComponent (s, (xs, flag)) =
    (s, (normaliseStates xs, flag))

normaliseBadComponent :: BadPairComponent -> BadPairComponent
normaliseBadComponent (pair, xs) =
    (pair, normaliseStates xs)

normaliseKHProductState :: KHProductState -> KHProductState
normaliseKHProductState st =
    KHProductState
        { seComponentsKH  = map normaliseSEComponent (seComponentsKH st)
        , badComponentsKH = map normaliseBadComponent (badComponentsKH st)
        }

allHaveSuccessor :: Relations -> [State] -> Action -> Bool
allHaveSuccessor rs xs a =
    all (hasSuccessor rs a) xs

hasSuccessor :: Relations -> Action -> State -> Bool
hasSuccessor rs a x =
    not (null (image (rA rs a) x))

stepSEComponent :: Relations -> Action -> SEComponent -> SEComponent
stepSEComponent rs a (s0, (xs, flag)) =
    case flag of
        SEBad ->
            (s0, (xs, SEBad))
        SEOk ->
            let okNext = allHaveSuccessor rs xs a
                xs'    = stepSet rs xs a
            in if okNext
               then (s0, (xs', SEOk))
               else (s0, (xs', SEBad))

stepBadComponent :: Relations -> Action -> BadPairComponent -> BadPairComponent
stepBadComponent rs a (pair, xs) =
    (pair, stepSet rs xs a)

initialKHProductState :: [State] -> [State] -> KHProductState
initialKHProductState phiStates negPsiStates =
    normaliseKHProductState $
        KHProductState
            { seComponentsKH =
                [ (s, ([s], SEOk))
                | s <- phiStates
                ]
            , badComponentsKH =
                [ ((t1, t2), [t1])
                | t1 <- phiStates
                , t2 <- negPsiStates
                ]
            }

acceptingKHProductState :: KHProductState -> Bool
acceptingKHProductState st =
    all seAccepts (seComponentsKH st)
    && all badPairAccepts (badComponentsKH st)
  where
    seAccepts :: SEComponent -> Bool
    seAccepts (_, (_, flag)) =
        flag == SEOk

    badPairAccepts :: BadPairComponent -> Bool
    badPairAccepts ((_, badTarget), xs) =
        badTarget `notElem` xs

stepKHProductState :: Relations -> Action -> KHProductState -> KHProductState
stepKHProductState rs a st =
    normaliseKHProductState $
        KHProductState
            { seComponentsKH =
                map (stepSEComponent rs a) (seComponentsKH st)
            , badComponentsKH =
                map (stepBadComponent rs a) (badComponentsKH st)
            }

khComplete :: AbilityMap -> [State] -> [State] -> Bool
khComplete m phiStates psiStates =
    existsReachable acceptingKHProductState next initialState
  where
    rs :: Relations
    rs = transitions m

    acts :: [Action]
    acts = actionsOf rs

    allStates :: [State]
    allStates = toList (states m)

    negPsiStates :: [State]
    negPsiStates =
        [ s | s <- allStates, s `notElem` psiStates ]

    initialState :: KHProductState
    initialState =
        initialKHProductState phiStates negPsiStates

    next :: KHProductState -> [KHProductState]
    next current =
        [ stepKHProductState rs a current
        | a <- acts
        ]

findWitnessPSpaceBySets :: AbilityMap -> [State] -> [State] -> Maybe Plan
findWitnessPSpaceBySets m phiStates psiStates =
    pathTo acceptingKHProductState next initialState
  where
    rs :: Relations
    rs = transitions m

    acts :: [Action]
    acts = actionsOf rs

    allStates :: [State]
    allStates = toList (states m)

    negPsiStates :: [State]
    negPsiStates =
        [ s | s <- allStates, s `notElem` psiStates ]

    initialState :: KHProductState
    initialState =
        initialKHProductState phiStates negPsiStates

    next :: KHProductState -> [(Action, KHProductState)]
    next current =
        [ (a, stepKHProductState rs a current)
        | a <- acts
        ]

truthSet :: AbilityMap -> Form -> [State]
truthSet m f =
    [ s | s <- toList (states m), isTrue (m, s) f ]

isTrue :: (AbilityMap, State) -> Form -> Bool
isTrue _ T = True
isTrue (m, s) (P p) =
    p `elem` valuationAt (valuation m) s
isTrue (m, s) (Neg f) =
    not (isTrue (m, s) f)
isTrue (m, s) (Conj f g) =
    isTrue (m, s) f && isTrue (m, s) g
isTrue (m, _) (KH f g) =
    khComplete m phiStates psiStates
  where
    phiStates = truthSet m f
    psiStates = truthSet m g

-- Infix alias for the complete satisfaction relation
(|=) :: (AbilityMap, State) -> Form -> Bool
(|=) = isTrue

findWitness :: AbilityMap -> Form -> Form -> Maybe Plan
findWitness m f g =
    findWitnessPSpaceBySets m phiStates psiStates
  where
    phiStates = truthSet m f
    psiStates = truthSet m g
\end{code}

\subsection{Parsing for $\mathcal{L}_{Kh}$}
Formulas may be created in \texttt{ghci} using \texttt{parseForm}. We omit most of the code here. The following inputs are accepted:

\begin{itemize}
    \item \texttt{p} or \texttt{P} followed by an integer $n$ returns \texttt{P n}
    \item \texttt{T} returns \texttt{T}
    \item \texttt{!p} returns \texttt{Neg p}
    \item \texttt{p \& q} returns \texttt{Conj p q}
    \item \texttt{KH p q} returns \texttt{KH p q}
    \item \texttt{p -> q} returns \texttt{Neg (Conj p (Neg q))} (as an abbreviation)
    \item \texttt{p v q} or \texttt{p V q} returns \texttt{Neg (Conj (Neg p) (Neg q))} (as an abbreviation)
\end{itemize}

\hide{
\begin{code}
pForm :: Parsec String () Form
pForm = spaces *> pImpl where
    -- Start parsing at implication level
    -- Abbreviation: Implication (right-associative)
    pImpl = chainr1 pDisj (spaces *> string "->" *> spaces >> return (\p q -> Neg (Conj p (Neg q))))

    -- Abbreviation: Disjunction (left-associative)
    pDisj = chainl1 pConj (spaces *> oneOf "vV" *> spaces >> return (\p q -> Neg (Conj (Neg p) (Neg q))))
    
    -- Conjunction (left-associative)
    pConj = chainl1 pPrefix (spaces *> char '&' *> spaces >> return Conj)

    pPrefix = try pNeg <|> try pKH <|> pTrue <|> pRemainder 

    -- Negation
    pNeg = char '!' >> spaces >> Neg <$> pPrefix
    
    -- Knowing How
    pKH = try (KH <$> (string "KH" >> spaces *> pPrefix) 
        <*> (spaces *> pPrefix))

    -- Truth-constant
    pTrue = char 'T' >> return T
    
    pRemainder = pVar <|> between (char '(' *> spaces) (spaces *> char ')') pForm
    pVar = spaces *> oneOf "pP" *> spaces *> (P . read <$> many1 digit) <* spaces
\end{code}
}
\begin{code}
parseForm :: String -> Either ParseError Form
parseForm = parse (pForm <* eof) "input"

evalForm :: (AbilityMap, State) -> String -> Bool
evalForm (m, s) str =
    case parseForm str of
        Right f -> isTrueBounded (m, s) f
        Left _  -> error "Invalid formula"

\end{code}

\subsection{Random Generation for $\mathcal{L}_{Kh}$}

\subsubsection{Model Generation with Parameters}\label{sec:LTSGen}
To facilitate testing with models of specific sizes, we implement a function that generates an \textit{AbilityMap} from a fixed number of states, propositions, and actions. 
We omit the code here.

The generated model includes:
\begin{itemize}
    \item a finite set of states $\{1,\dots,n\}$,
    \item a set of actions $\{1,\dots,k\}$,
    \item a valuation assigning each state a random subset of propositions $\{1,\dots,m\}$,
    \item a family of action-labelled transitions, each generated by randomly sampling pairs of states.
\end{itemize}
\hide{
\begin{code}
-- Generate an LTS with a specific number of states, propositions, and actions.
-- n: number of states
-- m: number of propositions
-- k: number of actions
generateLTS :: Int -> Int -> Int -> Gen AbilityMap
generateLTS n m k = do
    -- Ensure that the model has at least one state
    let n' = max 1 n
    let m' = max 0 m
    let k' = max 0 k

    let sts = [1 .. n']
    let stateList = head sts :| tail sts

    -- Available actions and propositions
    let actions = [1 .. fromIntegral k']
    let propRange = [1 .. m']

    -- Generate one random relation for each action
    rels <- mapM (\_ -> generateRandomRel sts) actions

    -- Generate one random valuation for each state
    vals <- mapM (generateRandomValuation propRange) sts

    return $ LTS stateList (zip actions rels) vals

-- Generate a random binary relation on the given set of states.
-- The relation is represented as a list of pairs (u,v).
generateRandomRel :: [State] -> Gen Rel
generateRandomRel sts = do
    -- Randomly decide how many edges to generate
    numEdges <- choose (0, length sts * length sts)

    -- Generate that many pairs of states
    edges <- vectorOf numEdges $ do
        u <- elements sts
        v <- elements sts
        return (u, v)

    -- Remove duplicates so that the relation behaves like a set
    return (nub edges)

-- Generate a random valuation for a state
-- by picking a random subset of the available propositions.
generateRandomValuation :: [Proposition] -> State -> Gen (State, [Proposition])
generateRandomValuation propRange s = do
    props <- sublistOf propRange
    return (s, props)
\end{code}
}
It is possible to generate concrete models and test formulas interactively in \texttt{ghci}. For instance:

\begin{verbatim}
ghci> m <- generate (generateLTS 5 3 2)
ghci> m
LTS {states = 1 :| [2,3,4,5], 
transitions = [(1,[(4,5),(4,2),(4,3),(5,1),(1,4),(2,2),
(3,1),(4,4),(2,3)]), (2,[(4,3),(4,5),(2,5),(4,2),(5,4),(1,5)])], 
valuation = [(1,[1,3]),(2,[2,3]),(3,[1,2,3]),(4,[2,3]),(5,[2])]}

-- Evaluate a formula at a state
ghci> isTrue (m, 1) (KH (P 1) (P 2))
True

-- Using the parser
ghci> evalForm (m, 1) "KH p1 p2"
True
\end{verbatim}

In the example above, \texttt{generateLTS 5 3 2} produces a random LTS with five states, three proposition letters, and two actions. The function \texttt{isTrue} can then be used to evaluate formulas directly, while \texttt{evalForm} allows testing formulas given as strings.

\subsubsection{Arbitrary Instances for QuickCheck}
Finally, for this section we define the instances of Arbitrary for \texttt{Form} and \texttt{Arbitrary} respectively. We omit the code here.

\hide{
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
}
It is possible to try out semantics by running \texttt{stack ghci}.
For example:\\

\begin{verbatim}
ghci> generate (arbitrary:: Gen AbilityMap)
LTS {states = 1 :| [2,3,4,5,6], ...
ghci> m = LTS {states = 1 :| [2,3,4,5,6], ...
ghci> isTrue (m, 2) (KH (P 4) (P 1))
False
ghci> evalForm (m, 2) "KH (p4 ^ !p2) p3"
True
\end{verbatim}