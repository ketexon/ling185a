module Assignment03 where

-- Imports everything from the FiniteState module
import FiniteState

-- A type we'll use as symbols for some FSAs
data SegmentPKIU = P | K | I | U | MB deriving (Show,Eq)

-- A list-like type that will be useful for computing forward values
data SnocList a = ESL | (SnocList a) ::: a deriving Show

-- The word ``hello'' encoded as a snoc list of characters
sl :: SnocList Char
sl = ((((ESL ::: 'h') ::: 'e') ::: 'l') ::: 'l') ::: 'o'

-- Checks that all states and symbols mentioned in the transition
-- table (i.e. delta) come from the provided lists of states and symbols.
fsaSanityCheck :: (Eq a) => Automaton a -> Bool
fsaSanityCheck m =
    let (states, syms, i, f, delta) = m in
    let validTransition (q1,x,q2) = elem q1 states && elem x syms && elem q2 states in
    and (map validTransition delta)

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.


-- 1 A
fsa_countVs :: Automaton SegmentCV
fsa_countVs = (
    [54, 73, 21, 38],   -- states
    [C, V],             -- alphabet
    [54],               -- initial states
    [38],               -- final states
    [                   -- transitinos
        (54, C, 54),
        (54, V, 73),
        (73, C, 73),
        (73, V, 21),
        (21, C, 21),
        (21, V, 54),
        (21, V, 38),
        (38, C, 38)
    ])


-- 2 B
addToFront :: a -> SnocList a -> SnocList a
addToFront v ESL = ESL ::: v
addToFront v (init' ::: last') = addToFront v init' ::: last'

-- 2 C
toSnoc :: [a] -> SnocList a
toSnoc l = toSnoc' $ reverse l
    where
        reverse [] = []
        reverse (x:xs) = reverse xs ++ [x]
        toSnoc' [] = ESL
        toSnoc' (x:xs) = toSnoc' xs ::: x

-- 2 D
forward :: (Eq a) => Automaton a -> SnocList a -> State -> Bool
forward (_, _, initials, _, _) ESL final = final `elem` initials
forward fsm (xs ::: x) final = tryForward states            -- iterate potential previous states
    where
        (states, _, initials, _, edges) = fsm
        tryForward [] = False
        tryForward (s:ss) = forward fsm xs s                -- if we can get from an initial state to s creating xs
                            && (s, x, final) `elem` edges   -- and we can go from s to final creating x
                            || tryForward ss                -- otherwise, check next state

-- 3 E
fsa_twoVs :: Automaton SegmentCV
fsa_twoVs = (
    [1, 2, 3],   -- states
    [C, V],             -- alphabet
    [1],               -- initial states
    [3],               -- final states
    [                   -- transitinos
        (1, C, 1),
        (1, V, 2),
        (2, C, 2),
        (2, V, 3),
        (3, C, 3),
        (3, V, 3)
    ])

-- 3 F
fsa_thirdlastC :: Automaton SegmentCV
fsa_thirdlastC = (
    [1, 2, 3, 4],   -- states
    [C, V],             -- alphabet
    [1],               -- initial states
    [4],               -- final states
    [                   -- transitinos
        (1, C, 1),
        (1, V, 1),
        (1, C, 2),
        (2, C, 3),
        (2, V, 3),
        (3, C, 4),
        (3, V, 4)
    ])


-- 3 G
fsa_oddEven :: Automaton SegmentCV
fsa_oddEven = (
    [1, 2, 3, 4],   -- states
    [C, V],             -- alphabet
    [1],               -- initial states
    [3],               -- final states
    [                   -- transitinos
        (1, V, 2),
        (2, V, 1),
        (1, C, 3),
        (3, C, 1),
        (2, C, 4),
        (4, C, 2),
        (3, V, 4),
        (4, V, 3)
    ])


-- 3 H
fsa_harmony :: Automaton SegmentPKIU
fsa_harmony = (
    [1,2,3],            -- states
    [P, K, I, U, MB],   -- alphabet
    [1],                -- initial states
    [1,2,3],            -- final states,
    [
        (1, P, 1),
        (1, K, 1),
        (1, MB, 1),

        (1, I, 2),
        (1, U, 3),

        (2, P, 2),
        (2, K, 2),
        (2, I, 2),

        (2, MB, 1),

        (3, P, 3),
        (3, K, 3),
        (3, U, 3),

        (3, MB, 1)
    ])



-- 3 I
fsa_MBU :: Automaton SegmentPKIU
fsa_MBU = (
    [1,2],            -- states
    [P, K, I, U, MB],   -- alphabet
    [1],                -- initial states
    [1,2],            -- final states,
    [
        (1, P, 1),
        (1, K, 1),
        (1, I, 1),

        (1, MB, 2),

        (2, P, 2),
        (2, K, 2),
        (2, I, 2),
        (2, U, 2),
        (2, MB, 2)
    ])

-- 4 J
-- There are n + 1 equivalence classes
--      0. Strings that contain no Vs
--      1. Strings that contain 1 V
--      ...
--      n. Strings that contain n Vs
-- In state j, C -> j and V -> j + 1, unless j == n, then C -> j and V goes nowhere
requireVs :: Int -> Automaton SegmentCV
requireVs n = (
    [0..n],             -- states
    [C, V],             -- alphabet
    [0],                -- initial states
    [n],              -- final states,
    (map (\i -> (i, C, i)) [0..n]) -- for state i, C -> i
        ++ (map (\i -> (i, V, i + 1)) [0..n-1]) -- for state i != n, V -> i + 1
    )


forward2 :: (Eq a) => Automaton a -> SnocList a -> State -> Bool
forward2 m w q = let (states, syms, i, f, delta) = m in
    case w of
        ESL -> elem q i
        rest:::x -> or( map (\q' -> elem (q', x, q) delta && forward2 m rest q') states)