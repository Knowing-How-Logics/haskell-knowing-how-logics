\section{Web Interface}\label{sec:WebInterface}

In this section we introduce a web-application to demo our code.
The web-app is consistent of a single page allowing users to do the following:
\begin{itemize}
    \item Parse single or multi agent formulas to our Haskell syntax
    \item Generate random single agent formulas in our Haskell syntax
    \item Generate single or multi agent models in our Haskell syntax using size-parameters
    \item Generate random single agent models in our Haskell syntax
\end{itemize}

The app also provides instructions on how to model-check.

Providing a user-interface (UI) is an additional feature to our project. 
Therefore we have kept our implementation extremely simple. 
We use a simple lightweight RESTful framework called scotty, and plain HTML and CSS is used for layout and styling. 
We serve a single plain JavaScript script to connect the UI to our Haskell code. 

The web-app is currently not deployed to the web. However, it is possible to run the app by running \verb|stack build| and \verb|stack run|.

\begin{code}
-- To allows Text to be interpreted as String
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Web.Scotty
import Network.Wai.Middleware.Static
import Data.Text.Lazy (pack)
import Test.QuickCheck (generate, arbitrary, Gen)
import SingleAgent (parseForm, Form, AbilityMap, generateLTS)
import MultiAgent(parseRegForm, generateRegLTSU)

main :: IO ()
main = scotty 3000 $ do
  middleware $ staticPolicy (noDots >-> addBase "static")

  get "/" $ do
    file "static/index.html"
  
  post "/parse-formula" $ do
    formula <- formParam "formula"        :: ActionM String
    language   <- formParam "language"    :: ActionM String

    let parsedForm = case language of
          "single"  -> show <$> parseForm formula
          "multi"   -> show <$> parseRegForm formula
          _ -> error "Invalid formula"

    text $ pack $ either (\e -> "Parse error: " ++ show e) id parsedForm
  
  post "/parse-model" $ do
    states <- formParam "states"          :: ActionM Int
    actions <- formParam "actions"        :: ActionM Int
    props <- formParam "props"            :: ActionM Int
    agents <- formParam "agents"          :: ActionM Int
    language   <- formParam "language"    :: ActionM String

    modelStr <- liftAndCatchIO $ case language of
      "single" -> do
        m <- generate $ generateLTS states actions props
        return (show m)
      "multi" -> do
        m <- generate $ generateRegLTSU states props actions agents
        return (show m)
      _ -> return "Invalid language"

    text $ pack modelStr

  get "/random-formula" $ do
    formula <- liftAndCatchIO $ generate (arbitrary :: Gen Form)
    text $ pack (show formula)
  
  get "/random-model" $ do
    model <- liftAndCatchIO $ generate (arbitrary :: Gen AbilityMap)
    text $ pack (show model)
\end{code}