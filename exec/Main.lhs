\section{Web Interface}\label{sec:WebInterface}

In this section we introduce a web-application to demo our code.
The web=app is consistent of a single page allowing users to do the following:
\begin{itemize}
    \item Parse single or multi agent formulas to our Haskell syntax
\end{itemize}

Our implementation is extremly simple. We use a simple lightweight RESTful framework called scotty. 
Plain HTML and CSS is used for layout and styling. 
We serve a single plain JavaScript script to connect the UI to our Haskell code. 


\begin{code}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Web.Scotty
import Network.Wai.Middleware.Static
import Data.Text.Lazy (pack)
import SingleAgent (parseForm)
import MultiAgent(parseRegForm)

main :: IO ()
main = scotty 3000 $ do
  middleware $ staticPolicy (noDots >-> addBase "static")

  get "/" $ do
    file "static/index.html"
  
  post "/haskell/parse-formula" $ do
    formula <- formParam "formula" :: ActionM String
    state   <- formParam "state"   :: ActionM String

    let parseResult = case state of
                "single"  -> show <$> parseForm formula
                "multi"   -> show <$> parseRegForm formula
                _ -> error "Invalid formula"

    text $ pack $ either (\e -> "Parse error: " ++ show e) id parseResult
\end{code}