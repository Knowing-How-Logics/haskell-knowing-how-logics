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