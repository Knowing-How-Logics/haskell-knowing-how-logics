\section{Testing and Validation}
\label{sec:semanticstests}

We now use the library \texttt{QuickCheck} to randomly generate models and states in order to test several basic semantic and implementation-level properties of both the basic single-agent logic \(\mathcal{L}_{Kh}\) and the multi-agent regular plan logic \(reg\text{-}\mathcal{L}^U_{Kh}\).

To perform these tests, we first define auxiliary types \texttt{PointedModel} (for single-agent models) and \texttt{PointedRegModel} (for multi-agent models), together with their \texttt{Arbitrary} instances. This allows \texttt{QuickCheck} to choose a random evaluation point inside a randomly generated model.


\subsection{Tests for \(\mathcal{L}_{Kh}\)}

We begin by testing several basic properties of the single-agent logic.

The first group of tests concerns the Boolean fragment:

\begin{itemize}
    \item Double Negation Elimination: \(\neg\neg\varphi \equiv \varphi\)
    \item Commutativity of Conjunction: \(\varphi \wedge \psi \equiv \psi \wedge \varphi\)
    \item Identity of Conjunction: \(\varphi \wedge \top \equiv \varphi\)
\end{itemize}

We then test a property specific to the \(Kh\)-modality. In our semantics, \(Kh(\psi,\varphi)\) is \emph{global}: its truth value does not depend on the current evaluation state, since its semantic clause quantifies over all states satisfying the precondition \(\psi\). Hence, if \(Kh(\psi,\varphi)\) holds at one state of a model, it should hold at every state of that model.

Finally, we test two basic implementation-level properties concerning plans: executing the empty plan should leave the current state unchanged, and the empty plan should be strongly executable at every state.\\


\subsection{Tests for \(reg\text{-}\mathcal{L}^U_{Kh}\)}

In the multi-agent setting, we test several basic semantic and implementation-level properties of the \(Kh_i\)-modality.

First, we test the case of an impossible precondition. If the precondition is contradictory, then no states satisfy it, and both semantic conditions of \(Kh_i(\psi,\varphi)\) are trivially satisfied. Hence, \(Kh_i(\psi,\varphi)\) should hold vacuously in this case.

Second, as in the single-agent case, we verify that \(Kh_i(\psi,\varphi)\) is global in the model: its truth value does not depend on the evaluation state, since its semantics quantifies over all states satisfying the precondition.

Finally, we include two implementation-level checks related to the automata-based part of the model checker. We first verify that the procedure \texttt{intersectionNonEmpty} is symmetric in its two automaton arguments. We also test that the path automata constructed in the implementation faithfully mirror the transition structure of the underlying LTS.


% \subsection{Test Implementation}
% We now present the HSpec and QuickCheck implementation of the test suite described above.\\
\hide{
\begin{code}
module Main where

import Test.QuickCheck
import Test.Hspec
import Data.List.NonEmpty (toList)

import SingleAgent
import MultiAgent
\end{code}

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


\begin{code}
-- Helper: check if two formulas are equivalent at a specific point
isEquivalent :: (AbilityMap, State) -> Form -> Form -> Bool
isEquivalent (m, s) f1 f2 = isTrue (m, s) f1 == isTrue (m, s) f2

\end{code}

\begin{code}

-- A contradictory formula, used as bottom
bottomReg :: RegForm
bottomReg = Not (Disj (Prop 1) (Not (Prop 1)))

-- Helper: number of agents in a reg-LTS^U model, used to ensure that generated formulas only refer to valid agent indices
numAgentsIn :: RegLTSU -> Int
numAgentsIn m = length (uncertainty m)


\end{code}

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

    it "Kh is global: truth does not vary between states" $
      property $ \m f g ->
      let sts = toList (states m)
          results = [ isTrue (m, s) (KH f g) | s <- sts ]
      in all (== head results) results

    it "Empty plan leaves the current state unchanged" $
      property $ \(PM (m, s)) ->
        executePlan (transitions m) s [] == [s]

    it "Empty plan is strongly executable at every state" $
        property $ \(PM (m, s)) ->
          stronglyExecutableAt (transitions m) s []

  describe "Multi-Agent Logic reg-L^U_KH" $ do

  

    it "Vacuous Precondition: knowing how from contradiction holds vacuously" $
      property $ \(PRM (m, s)) agent ->
        let nA = numAgentsIn m
        in forAll (sized (generateRegForm nA)) $ \phi ->
           let aIdx = (agent `mod` nA) + 1
           in isTrueReg (m, s) (KHI aIdx bottomReg phi)

    it "Kh_i is global: agent ability is a model-wide property" $
      property $ \(PRM (m, _)) agent ->
        let nA = numAgentsIn m
        in forAll (sized (generateRegForm nA)) $ \f ->
           forAll (sized (generateRegForm nA)) $ \g ->
             let aIdx = (agent `mod` nA) + 1
                 sts = statesM m
                 results = [ isTrueReg (m, s) (KHI aIdx f g) | s <- sts ]
             in not (null results) ==> all (== head results) results

    it "Intersection checking is symmetric: the intersection of L(A1) and L(A2) is non-empty iff the intersection of L(A2) and L(A1) is non-empty" $
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

    it "Path automata mirror the LTS transitions" $
      property $ \(PRM (m, _)) ->
        forAll (elements (statesM m)) $ \t1 ->
        forAll (elements (statesM m)) $ \t2 ->
          let aut = buildPathAutomaton m t1 t2
          in conjoin
              [ getAutNext aut s a === getLtsNext m s a
              | s <- statesM m
              , a <- actionsA aut
              ]

\end{code}
}


Running \texttt{stack test} in the terminal yields the following relevant test output.

\begin{verbatim}
KHora> test (suite: quickcheck-logic)
                   
Single-Agent Logic L_Kh
  Boolean: Double Negation Elimination (!!f <=> f) 
    +++ OK, passed 100 tests.
  Boolean: Commutativity of Conjunction (f1 ^ f2 <=> f2 ^ f1) 
    +++ OK, passed 100 tests.
  Boolean: Identity of Conjunction (f ^ T <=> f) 
    +++ OK, passed 100 tests.
  Kh is global: truth does not vary between states 
    +++ OK, passed 100 tests.
  Empty plan leaves the current state unchanged
    +++ OK, passed 100 tests.
  Empty plan is strongly executable at every state 
    +++ OK, passed 100 tests.
Multi-Agent Logic reg-L^U_KH
  Vacuous Precondition: knowing how from contradiction holds vacuously 
    +++ OK, passed 100 tests.
  Kh_i is global: agent ability is a model-wide property 
    +++ OK, passed 100 tests.
  Intersection checking is symmetric: 
  the intersection of L(A1) and L(A2) is non-empty 
  iff the intersection of L(A2) and L(A1) is non-empty
    +++ OK, passed 100 tests.
  Path automata mirror the LTS transitions 
    +++ OK, passed 100 tests.

Finished in 1.1135 seconds
10 examples, 0 failures

KHora> Test suite quickcheck-logic passed
Completed 2 action(s).
\end{verbatim}


Overall, these results provide evidence that the implementation correctly captures the intended semantic and implementation-level properties of the logics.
