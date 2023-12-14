module Test where

import CFGParsing

-- data Cat = S | NP | VP | PP | N | V | P | WHILE | POSS | ORC | SRC
--              | THAT | OR | AND | D | A deriving (Show, Eq, Ord)

rules1 :: [RewriteRule Cat String]
rules1
    = [
        TRule WHILE "while"
        , TRule POSS "'s"
        , TRule THAT "that"
        , TRule OR "or"
        , TRule AND "and"
        , TRule D "the"

        , TRule N "cat"

        , NTRule NP [D, N]
    ]
