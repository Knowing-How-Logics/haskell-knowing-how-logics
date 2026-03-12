\section{Tests for Boolen semantics}
\label{sec:booltests}
We now use the library QuickCheck to randomly generate models and states to verify
the fundamental logical facts within the boolean fragment of our implementation.

\begin{code}
module Main where

import Test.QuickCheck
import Data.List.NonEmpty (toList)
import KnowingHow
import Test.Hspec
\end{code}

The following uses the HSpec library to define our test suite. These tests ensure
that our model checker respects classical propositional identities. To perform
these tests, we first define an auxiliary type \texttt{PointedModel} and an
\texttt{Arbitrary} instance to pick a random state from a generated model.

\begin{code}
newtype PointedModel = PM (AbilityMap, State) deriving (Show)

instance Arbitrary PointedModel where
    arbitrary = do
        m <- arbitrary
        s <- elements (toList (states m))
        return (PM (m, s))
\end{code}

We verify the following principles which should hold for any boolean formula $\varphi$:

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

\begin{code}
-- Since Kh is currently undefined, we use a helper function to filter out formulas containing the Kh modality.
isBoolean :: Form -> Bool
isBoolean (P _)        = True
isBoolean T            = True
isBoolean (Neg f)      = isBoolean f
isBoolean (Conj f1 f2) = isBoolean f1 && isBoolean f2
isBoolean (KH _ _)     = False

-- Check if two formulas are equivalent in a specific model and state
isEquivalent :: (AbilityMap, State) -> Form -> Form -> Bool
isEquivalent (m, s) f1 f2 = isTrue (m, s) f1 == isTrue (m, s) f2

main :: IO ()
main = hspec $ do
  describe "Boolean Semantics" $ do
    it "Double Negation Elimination: Neg (Neg f) should be equivalent to f" $
      property $ \(PM (m, s)) f -> 
        isBoolean f ==> isEquivalent (m, s) (Neg (Neg f)) f

    it "Commutativity of Conjunction: f1 ^ f2 should be equivalent to f2 ^ f1" $
      property $ \(PM (m, s)) f1 f2 -> 
        (isBoolean f1 && isBoolean f2) ==> isEquivalent (m, s) (Conj f1 f2) (Conj f2 f1)

    it "Identity of Conjunction: f ^ T should be equivalent to f" $
      property $ \(PM (m, s)) f -> 
        isBoolean f ==> isTrue (m, s) (Conj f T) === isTrue (m, s) f
\end{code}


