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


\hide{
\begin{code}
module BasicKH where

import Data.List (nub, sort)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Text.Parsec hiding (State)
import LTS
import GraphSearch
\end{code}
}

\begin{code}
data Form = P Proposition | Neg Form | Conj Form Form | KH Form Form | T
    deriving (Eq, Show, Ord)

\end{code}


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

findWitnessPSpaceBySets :: AbilityMap -> [State] -> [State] -> Maybe Plan
findWitnessPSpaceBySets m phiStates psiStates =
    pathTo acceptingKHProductState next initialState
  where
    rs :: Relations
    rs =
        transitions m

    acts :: [Action]
    acts =
        actionsOf rs

    allStates :: [State]
    allStates =
        toList (states m)

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

khHoldsByProductSearch :: AbilityMap -> [State] -> [State] -> Bool
khHoldsByProductSearch m phiStates psiStates =
    case findWitnessPSpaceBySets m phiStates psiStates of
        Just _ ->
            True
        Nothing ->
            False

truthSet :: AbilityMap -> Form -> [State]
truthSet m f =
    [ s | s <- toList (states m), isTrue (m, s) f ]

isTrue :: (AbilityMap, State) -> Form -> Bool
isTrue _ T =
    True
isTrue (m, s) (P p) =
    p `elem` valuationAt (valuation m) s
isTrue (m, s) (Neg f) =
    not (isTrue (m, s) f)
isTrue (m, s) (Conj f g) =
    isTrue (m, s) f && isTrue (m, s) g
isTrue (m, _) (KH f g) =
    khHoldsByProductSearch m phiStates psiStates
  where
    phiStates =
        truthSet m f

    psiStates =
        truthSet m g

-- Infix alias for the complete satisfaction relation
(|=) :: (AbilityMap, State) -> Form -> Bool
(|=) = isTrue

findWitness :: AbilityMap -> Form -> Form -> Maybe Plan
findWitness m f g =
    findWitnessPSpaceBySets m phiStates psiStates
  where
    phiStates =
        truthSet m f

    psiStates =
        truthSet m g
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
        Right f ->
            isTrue (m, s) f
        Left _ ->
            error "Invalid formula"

\end{code}

