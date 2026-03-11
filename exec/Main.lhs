
This \texttt{Main} module serves as the entry point for our test suite. It imports the core logic from the library and defines the properties to be verified by QuickCheck.

\begin{code}
module Main where

import Test.QuickCheck
import Data.List.NonEmpty (toList)
import KnowingHow
\end{code}

Now we use QuickCheck to verify fundamental logical facts within the boolean fragment of our implementation. 
These tests ensure that our model checker respects classical propositional identities. 
To perform these tests, we must first define an instance to pick a random state from a generated model.

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

-- Double Negation Elimination
propDoubleNegation :: PointedModel -> Form -> Property
propDoubleNegation (PM (m, s)) f = 
    isBoolean f ==> isEquivalent (m, s) (Neg (Neg f)) f

-- Commutativity of Conjunction
propCommutativityOfConjunction :: PointedModel -> Form -> Form -> Property
propCommutativityOfConjunction (PM (m, s)) f1 f2 = 
    (isBoolean f1 && isBoolean f2) ==> isEquivalent (m, s) (Conj f1 f2) (Conj f2 f1)

-- Identity of Conjunction
propIdentityOfConjunction :: PointedModel -> Form -> Property
propIdentityOfConjunction (PM (m, s)) f = 
    isBoolean f ==> isTrue (m, s) (Conj f T) === isTrue (m, s) f
\end{code}

To execute the verification suite, we define a \texttt{main} function that invokes the QuickCheck runner for each of our logical facts. 

\begin{code}
main :: IO ()
main = do
    putStrLn "--- Testing Boolean Fragment of Knowing How Logic ---"
    
    putStrLn "Double Negation Elimination"
    quickCheck propDoubleNegation
    
    putStrLn "Commutativity of Conjunction"
    quickCheck propCommutativityOfConjunction
    
    putStrLn "Identity of Conjunction"
    quickCheck propIdentityOfConjunction
    
    putStrLn "--- All Boolean tests completed ---"
\end{code}



%\section{Wrapping it up in an exectuable}\label{sec:Main}

%We will now use the library form Section \ref{sec:Basics} in a program.

%\begin{code}
%module Main where

%import Basics

%main :: IO ()
%main = do
%  putStrLn "Hello!"
  %print somenumbers
  %print (map funnyfunction somenumbers)
  %myrandomnumbers <- randomnumbers
  %print myrandomnumbers
  %print (map funnyfunction myrandomnumbers)
  %putStrLn "GoodBye"
%\end{code}

%We can run this program with the commands:

%\begin{verbatim}
%stack build
%stack exec myprogram
%\end{verbatim}

%The output of the program is something like this:

%\begin{verbatim}
%Hello!
%[1,2,3,4,5,6,7,8,9,10]
%[100,100,300,300,500,500,700,700,900,900]
%[1,3,0,1,1,2,8,0,6,4]
%[100,300,42,100,100,100,700,42,500,300]
%GoodBye
%\end{verbatim}