\section{Testing and Validation}
\label{sec:semanticstests}

We now use the library QuickCheck to randomly generate models and states in order to test central semantic properties of both the basic single-agent logic \(\mathcal{L}_{Kh}\) and the multi-agent regular plan logic \(reg\text{-}\mathcal{L}^U_{KH}\).\\

\begin{code}
module Main where

import Test.QuickCheck
import Test.Hspec
import Data.List.NonEmpty (toList)

import SingleAgent
import MultiAgent
\end{code}

The following uses the HSpec library to define our test suite.

To perform these tests, we first define auxiliary types \texttt{PointedModel} (for single-agent models) and \texttt{PointedRegModel} (for multi-agent models), together with their \texttt{Arbitrary} instances. This allows QuickCheck to select a random evaluation point inside a randomly generated model.\\

\begin{code}
-- Pointed model for single-agent L_Kh
newtype PointedModel = PM (AbilityMap, State) deriving (Show)

instance Arbitrary PointedModel where
    arbitrary = do
        m <- arbitrary
        s <- elements (toList (states m))
        return (PM (m, s))

-- Pointed model for multi-agent reg-LTS^U
newtype PointedRegModel = PRM (RegLTSU, State) deriving (Show)

instance Arbitrary PointedRegModel where
    arbitrary = do
        nStates <- chooseInt (1, 3)
        nProps  <- chooseInt (1, 3)
        nActs   <- chooseInt (1, 3)
        nAgents <- chooseInt (1, 3)
        m <- generateRegLTSU nStates nProps nActs nAgents
        s <- elements (statesM m)
        return (PRM (m, s))
\end{code}

\subsection{Tests for \(\mathcal{L}_{Kh}\)}

We first test some basic properties of the single-agent logic. 

The first group concerns the Boolean fragment. 

\begin{itemize}
    \item \textbf{Double Negation Elimination}
    \begin{itemize}
        \item $\neg\neg\varphi \equiv \varphi$
    \end{itemize}
    \item \textbf{Commutativity of Conjunction}
    \begin{itemize}
        \item $\varphi \wedge \psi \equiv \psi \wedge \varphi$
    \end{itemize}
    \item \textbf{Identity of Conjunction}
    \begin{itemize}
        \item $\varphi \wedge \top \equiv \varphi$
    \end{itemize}
\end{itemize}

We then test a property specific to \(Kh\). 
We verify that \(Kh(\psi,\varphi)\) is \emph{global}: its truth value does not depend on the current evaluation state, since its semantic clause quantifies over all states satisfying the precondition \(\psi\). Therefore, if \(Kh(\psi,\varphi)\) holds at one state of a model, it should hold at every state of that model.\\


\begin{code}
-- Helper: check if two formulas are equivalent at a specific point
isEquivalent :: (AbilityMap, State) -> Form -> Form -> Bool
isEquivalent (m, s) f1 f2 = isTrue (m, s) f1 == isTrue (m, s) f2

\end{code}

\subsection{Tests for \(reg\text{-}\mathcal{L}^U_{KH}\)}

In the multi-agent setting, we test several central semantic properties of the \(Kh_i\)-modality.

We test the case of an \textbf{impossible precondition}. If the precondition is contradictory, then no states satisfy it, and both semantic conditions of \(Kh_i(\psi,\varphi)\) are trivially satisfied. Hence, \(Kh_i(\psi,\varphi)\) should hold vacuously in this case.

As in the single-agent case, we verify that \(Kh_i(\psi,\varphi)\) is \textbf{global} in the model: its truth value does not depend on the evaluation state, since its semantics quantifies over all states satisfying the precondition.

Finally, we include a test at the level of the underlying automata machinery. In particular, we verify that the check for non-emptiness of language intersection between automata is symmetric. \\

\begin{code}
-- Helper: universal implication in multi-agent models
isUniversallyImpliedReg :: RegLTSU -> RegForm -> RegForm -> Bool
isUniversallyImpliedReg m psi phi =
    all (\s -> not (isTrueReg (m, s) psi) || isTrueReg (m, s) phi) (statesM m)

-- A contradictory formula, used as bottom
bottomReg :: RegForm
bottomReg = Not (Disj (Prop 1) (Not (Prop 1)))

-- Helper: number of agents in a reg-LTS^U model, used to ensure that generated formulas only refer to valid agent indices
numAgentsIn :: RegLTSU -> Int
numAgentsIn m = length (uncertainty m)


\end{code}

\subsection{HSpec Test Suite}

The test suite below combines general Boolean checks with semantic properties that are characteristic of knowing-how logics.\\

\begin{code}
main :: IO ()
main = hspec $ do

  describe "Single-Agent Logic L_Kh" $ do

    it "Boolean: Double Negation Elimination (!!f <=> f)" $
      property $ \(PM (m, s)) f ->
        isEquivalent (m, s) (Neg (Neg f)) f

    it "Boolean: Commutativity of Conjunction (f1 ^ f2 <=> f2 ^ f1)" $
      property $ \(PM (m, s)) f1 f2 ->
        isEquivalent (m, s) (Conj f1 f2) (Conj f2 f1)

    it "Boolean: Identity of Conjunction (f ^ T <=> f)" $
      property $ \(PM (m, s)) f ->
        isTrue (m, s) (Conj f T) === isTrue (m, s) f

    it "KH is global: truth does not vary between states" $
      property $ \m f g ->
        let sts = toList (states m)
            results = [ isTrue (m, s) (KH f g) | s <- sts ]
        in not (null results) ==> all (== head results) results

  describe "Multi-Agent Logic reg-L^U_KH" $ do

  

    it "Vacuous Precondition: knowing how from contradiction holds vacuously" $
      property $ \(PRM (m, s)) agent ->
        let nA = numAgentsIn m
        in forAll (sized (generateRegForm nA)) $ \phi ->
           let aIdx = (agent `mod` nA) + 1
           in isTrueReg (m, s) (KHI aIdx bottomReg phi)

    it "KH_i is global: agent ability is a model-wide property" $
      property $ \(PRM (m, _)) agent ->
        let nA = numAgentsIn m
        in forAll (sized (generateRegForm nA)) $ \f ->
           forAll (sized (generateRegForm nA)) $ \g ->
             let aIdx = (agent `mod` nA) + 1
                 sts = statesM m
                 results = [ isTrueReg (m, s) (KHI aIdx f g) | s <- sts ]
             in not (null results) ==> all (== head results) results

    it "Intersection checking is symmetric: L(A1) intersect L(A2) is non-empty iff L(A2) intersect L(A1) is non-empty" $
      property $ \(PRM (m, _)) agent1 agent2 ->
        let nA    = numAgentsIn m
            aIdx1 = (agent1 `mod` nA) + 1
            aIdx2 = (agent2 `mod` nA) + 1
            auts1 = getAgentAuts m aIdx1
            auts2 = getAgentAuts m aIdx2
        in not (null auts1) && not (null auts2) ==>
           forAll (elements auts1) $ \aut1 ->
           forAll (elements auts2) $ \aut2 ->
             intersectionNonEmpty aut1 aut2
             ==
             intersectionNonEmpty aut2 aut1

\end{code}


Running \texttt{stack test} yields the following relevant test output.

\begin{verbatim}
report> test (suite: quickcheck-logic)
                    

Single-Agent Logic L_Kh
  Boolean: Double Negation Elimination (!!f <=> f) 
    +++ OK, passed 100 tests.
  Boolean: Commutativity of Conjunction (f1 ^ f2 <=> f2 ^ f1)
    +++ OK, passed 100 tests.
  Boolean: Identity of Conjunction (f ^ T <=> f) 
    +++ OK, passed 100 tests.
  KH is global: truth does not vary between states 
    +++ OK, passed 100 tests.
Multi-Agent Logic reg-L^U_KH
  Vacuous Precondition: knowing how from contradiction holds vacuously 
    +++ OK, passed 100 tests.
  KH_i is global: agent ability is a model-wide property
    +++ OK, passed 100 tests.
  Intersection checking is symmetric: 
  L(A1) intersect L(A2) is non-empty iff L(A2) intersect L(A1) is non-empty

Finished in 5.2967 seconds
7 examples, 0 failures
\end{verbatim}


Overall, these results provide further evidence that the implementation correctly captures central semantic features of knowing-how logics.