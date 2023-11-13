{-# LANGUAGE FlexibleInstances #-}

module Assignment05 where

import Control.Applicative(liftA, liftA2, liftA3)

import SemiringFSA

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

-- 1A
backward :: (Semiring v) => GenericAutomaton st sy v -> [sy] -> st -> v
backward (_, _, _, final_v, _) [] final_state
    = final_v final_state

backward automaton (x:xs) final_state
    = gen_or $ (\state -> transition_v (final_state, x, state) &&& backward automaton xs state) <$> states
    where
        (states, syms, _, final_v, transition_v) = automaton

-- 1B
f :: (Semiring v) => GenericAutomaton st sy v -> [sy] -> v
f automaton str
    = gen_or $ (\st -> initial_v st &&& backward automaton str st) <$> states
    where
        (states, syms, initial_v, _, transition_v) = automaton

-- 1C
addCosts :: Cost -> Cost -> Cost
addCosts (TheInt a) (TheInt b) = TheInt $ a + b
addCosts _ Inf = Inf
addCosts Inf _ = Inf

-- 1D
minCost :: Cost -> Cost -> Cost
minCost (TheInt a) (TheInt b) = TheInt $ min a b
minCost a Inf = a
minCost Inf b = b

maxCost :: Cost -> Cost -> Cost
maxCost (TheInt a) (TheInt b) = TheInt $ max a b
maxCost _ Inf = Inf
maxCost Inf _ = Inf

-- 1E
instance Semiring Cost where
    x &&& y = addCosts x y
    x ||| y = minCost x y
    gtrue = TheInt 0
    gfalse = Inf

-- 1F
instance Semiring [[a]] where
    x &&& y = (++) <$> x <*> y
    x ||| y = x ++ y
    gtrue = [[]]
    gfalse = []

-- 1G
gfsa34 :: GenericAutomaton Int Char [[Char]]
gfsa34
    = makeGFSA [] (
        [1,2,3],
        ['C','V'],
        [(1, [""])],
        [(1, [""])],
        [
            ((1,'V',1), ["V"]),
            ((1,'C',2), ["C"]),
            ((1,'V',3), ["V"]),
            ((2,'V',1), ["V", "VV"]),
            ((2,'V',3), ["V", "VV"]),
            ((3,'C',1), [""])
        ])

-- 1H
gfsa_flap :: GenericAutomaton Int Char [[Char]]
gfsa_flap
    = makeGFSA [] (
        [1,2,3],
        ['a','n','t'],
        [(1, [""])],
        [
            (1, [""]),
            (2, [""]),
            (3, ["t"])
        ],
        [
            ((1,'n',1), ["n"]),
            ((1,'t',1), ["t"]),

            ((1,'a',2), ["a"]),

            ((2,'n',1), ["n"]),
            ((2,'a',2), ["a"]),
            ((2,'t',3), [""]),

            ((3,'n',1), ["tn"]),
            ((3,'t',1), ["tt"]),
            ((3,'a',2), ["ta", "Ta"])
        ])

-- 1I
gfsa5_count :: GenericAutomaton Int Char Double
gfsa5_count
    = makeGFSA 0.0 (
        [1,2,3],
        ['C','V'],
        [(1, 1.0)],
        [(1, 1.0)],
        [
            ((1,'V',1), 1.0),
            ((1,'C',2), 1.0),
            ((1,'V',3), 1.0),
            ((2,'V',1), 1.0),
            ((2,'V',3), 1.0),
            ((3,'C',1), 1.0)
        ])

-- 1J
gfsa5_paths :: GenericAutomaton Int Char [[Int]]
gfsa5_paths
    = makeGFSA [] (
        [1,2,3],
        ['C','V'],
        [(1, [[1]])],
        [(1, [[]])],
        [
            ((1,'V',1), [[1]]),
            ((1,'C',2), [[2]]),
            ((1,'V',3), [[3]]),
            ((2,'V',1), [[1]]),
            ((2,'V',3), [[3]]),
            ((3,'C',1), [[1]])
        ])