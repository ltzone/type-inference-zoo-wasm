module Print (showTreeHtml, toNodeInfoTree) where

-- This code is from the Haskell package `tree-view`

-- Copyright (c) 2014, Emil Axelsson

-- All rights reserved.

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:

--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.

--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.

--     * Neither the name of Emil Axelsson nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.

-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import Control.Monad.State
  ( MonadState (get, put),
    State,
    evalState,
  )
import Data.Tree (Tree (Node))
import Data.Tree.View (Behavior (..), NodeInfo (..))

escapeBrackets :: String -> String
escapeBrackets = concatMap fixBrack
  where
    fixBrack '<' = "&lt;"
    fixBrack '>' = "&gt;"
    fixBrack c = [c]

htmlNode :: (NodeInfo, Int) -> String
htmlNode (n, i) =
  concat
    [ "<span id=\"node",
      show i,
      "\" class=\"node ",
      mode,
      "\"",
      onclick,
      "title=\"",
      nodeInfo n,
      "\"",
      ">",
      escapeBrackets $ nodeName n,
      "</span>"
    ]
  where
    mode = case nodeBehavior n of
      Fixed -> "fixed"
      InitiallyCollapsed -> "interactive collapsed"
      InitiallyExpanded -> "interactive expanded"
    onclick = case nodeBehavior n of
      Fixed -> " "
      _ -> " onclick=\"toggle(event)\" "

appLast :: [String] -> String -> [String]
appLast ss s = init ss ++ [last ss ++ s]

indentInit :: [String] -> [String]
indentInit [] = []
indentInit (s : ss) = (" ├╴" ++ s) : map (" │ " ++) ss

indentLast :: [String] -> [String]
indentLast [] = []
indentLast (s : ss) = (" └╴" ++ s) : map ("   " ++) ss

indentChildren :: [[String]] -> [[String]]
indentChildren [] = []
indentChildren ns = map indentInit (init ns) ++ [indentLast (last ns)]

enumTree :: Tree a -> Tree (a, Int)
enumTree = flip evalState 0 . traverse count
  where
    count :: a -> State Int (a, Int)
    count a = do
      i <- get
      put (i + 1)
      return (a, i)

showTreeHtml' :: Tree (NodeInfo, Int) -> [String]
showTreeHtml' (Node (n, i) []) = [htmlNode (n {nodeBehavior = Fixed}, i)]
showTreeHtml' (Node n ns) =
  ( htmlNode n
      ++ "<span id=\"children_node"
      ++ show (snd n)
      ++ "\" class="
      ++ display
      ++ ">"
  )
    : appLast (concat (indentChildren (map showTreeHtml' ns))) "</span>"
  where
    display = case nodeBehavior $ fst n of
      InitiallyCollapsed -> show "hidden"
      _ -> show "shown"

showTreeHtml :: Tree NodeInfo -> String
showTreeHtml = unlines . showTreeHtml' . enumTree


toNodeInfoTree :: Tree String -> Tree NodeInfo
toNodeInfoTree (Node s tree) = Node (NodeInfo InitiallyExpanded s "") $ map toNodeInfoTree tree
