module Assignment04 where

import Prelude hiding (Either(..))

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List(nub)

import FiniteStatePart2

---------------------------------------
-- Setup for section 1

type SLG sy = ([sy], [sy], [sy], [(sy,sy)])
data ConstructedState sy = ExtraState | StateForSymbol sy deriving (Eq, Show)

slg1 :: SLG SegmentCV
slg1 = ([C,V], [C], [V], [(C,C),(C,V),(V,V)])

slg2 :: SLG Int
slg2 = ([1,2,3], [1,2,3], [1,2,3], [(1,1),(2,2),(3,3),(1,2),(2,1),(1,3),(3,1)])

---------------------------------------
-- Setup for section 2

data Either a b = First a | Second b deriving (Show,Eq)

re1 :: RegExp Char
re1 = Concat (Alt (Lit 'a') (Lit 'b')) (Lit 'c')

re2 :: RegExp Char
re2 = Star re1

re3 :: RegExp Int
re3 = Star (Concat ZeroRE (Lit 3))

re4 :: RegExp Int
re4 = Concat (Alt (Lit 0) (Lit 1)) (Star (Lit 2))

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

-- 1A
backwardSLG :: (Eq sy) => SLG sy -> [sy] -> Bool
backwardSLG slg [] = False
backwardSLG (_, _, final, _) [sym] = sym `elem` final
backwardSLG slg (x:y:xs)
    = backwardSLG slg (y:xs) && (x, y) `elem` pairs
    where
        (syms, initial, final, pairs) = slg

generatesSLG :: (Eq sy) => SLG sy -> [sy] -> Bool
generatesSLG slg [] = False
generatesSLG (syms, initial, final, pairs) str
    = x `elem` initial
        && last str `elem` final
        -- for each consequetive pair `zip (init str) (xs)`
        -- check if it is an elem of `pairs` `(flip elem) pairs`
        -- and `and` the results
        && (and $ (flip elem) pairs <$> zip (str) (xs))
    where
        x:xs = str

generatesSLG2 :: (Eq sy) => SLG sy -> [sy] -> Bool
generatesSLG2 slg [] = False
generatesSLG2 slg str
    = backwardSLG slg str && x `elem` initial
    where
        (syms, initial, final, pairs) = slg
        x:_ = str


-- 1C
slgToFSA :: (Eq sy) => SLG sy -> Automaton (ConstructedState sy) sy
slgToFSA (syms, initial, final, pairs)
    = (states, syms, [ExtraState], finalStates, initialTransitions ++ medialTransitions)
    where
        states = ExtraState : (StateForSymbol <$> syms)
        finalStates = StateForSymbol <$> final
        initialTransitions = (\s -> (ExtraState, s, StateForSymbol s)) <$> initial
        medialTransitions = (\(x, y) -> (StateForSymbol x, y, StateForSymbol y)) <$> pairs


-- 2E
unionFSAs :: (Eq sy) => EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
unionFSAs fsaA fsaB
    = (
        fsaUnion statesA statesB,
        union symsA symsB,
        fsaUnion initialA initialB,
        fsaUnion finalA finalB,
        transitions
        )
    where
        (statesA, symsA, initialA, finalA, transitionsA) = fsaA
        (statesB, symsB, initialB, finalB, transitionsB) = fsaB
        fsaUnion a b = (First <$> a) ++ (Second <$> b)
        transitions = ((\(s1, sym, s2) -> (First s1, sym, First s2)) <$> transitionsA)
                        ++ ((\(s1, sym, s2) -> (Second s1, sym, Second s2)) <$> transitionsB)


-- 2F
concatFSAs :: EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
concatFSAs fsaA fsaB
    = (
        (First <$> statesA) ++ (Second <$> statesB),
        union symsA symsB,
        (First <$> initialA), -- start at fsaA
        (Second <$> finalB), -- end at end of fsaB
        transitions
        )
    where
        (statesA, symsA, initialA, finalA, transitionsA) = fsaA
        (statesB, symsB, initialB, finalB, transitionsB) = fsaB
        transitions = ((\(s1, sym, s2) -> (First s1, sym, First s2)) <$> transitionsA) -- transitions within fsaA
                        ++ ((\(s1, sym, s2) -> (Second s1, sym, Second s2)) <$> transitionsB) -- transitions within fsaB
                        -- transitions from fsaA to fsaB
                        -- maps final states s of fsaA to function (s,Nothing,)
                        -- applies functino to each element of fsaB's initial
                        ++ ((,Nothing,) <$> (First <$> finalA) <*> (Second <$> initialB))



-- 2G
starFSA :: EpsAutomaton st sy -> EpsAutomaton (Either Int st) sy
starFSA (states, syms, initial, final, transitions) =
    (
        newInitialState:(Second <$> states),
        syms,
        [newInitialState],
        [newInitialState],
        newTransitions
    )
    where
        newInitialState = First 0
        newTransitions = ((\(a, sym, b) -> (Second a, sym, Second b)) <$> transitions)
                            ++ ((newInitialState, Nothing,) <$> Second <$> initial) -- new initial state goes to all initial states
                            ++ ((,Nothing,newInitialState) <$> Second <$> final) -- final states go to new initial state

-- 2H
flatten :: Either Int Int -> Int
flatten (First x) = 2 * x
flatten (Second x) = 2 * x + 1

-- 2I
mapStates :: (a -> b) -> EpsAutomaton a sy -> EpsAutomaton b sy
mapStates f (states, syms, initial, final, transitions)
    = (
        f <$> states,
        syms,
        f <$> initial,
        f <$> final,
        (\(a, sym, b) -> (f a, sym, f b)) <$> transitions
    )

-- 2J
reToFSA :: (Eq sy) => RegExp sy -> EpsAutomaton Int sy
reToFSA (Lit lit)
    = (
        [0, 1],
        [lit],
        [0],
        [1],
        [(0, Just lit, 1)]
    )

reToFSA (Alt reA reB)
    = mapStates flatten (unionFSAs (reToFSA reA) (reToFSA reB))
reToFSA (Concat reA reB)
    = mapStates flatten (concatFSAs (reToFSA reA) (reToFSA reB))
reToFSA (Star re)
    = mapStates flatten (starFSA (reToFSA re))
reToFSA ZeroRE -- FSA with no initial state -> generates nothing
    = (
        [],
        [],
        [],
        [],
        []
    )
reToFSA OneRE -- FSA with no transitions but with an initial and final state -> generates empty string
    = (
        [0],
        [],
        [0],
        [0],
        []
    )