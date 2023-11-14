{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}

module ContextFree where

import Control.Applicative(liftA, liftA2, liftA3)

import qualified Memoization as M

data Cat = S | NP | VP | PP | V | P deriving (Show, Eq, Ord)

data RewriteRule nt t = NTRule nt (nt,nt) | TRule nt t deriving (Show, Eq)
-- A -> B C
-- A -> x

-- Corresponds to the definition in (3) on the handout
type CFG nt t = ([nt], [t], [nt], [RewriteRule nt t])

-----------------------------------------------------------
-- CFGs generalized to allow non-boolean result values

type GenericCFG nt t v = ([nt], [t], nt -> v, RewriteRule nt t -> v)

-- Feel free to ignore the details of this function.
makeGCFG :: (Eq nt, Eq t) => v -> ([nt], [t], [(nt,v)], [(RewriteRule nt t, v)]) -> GenericCFG nt t v
makeGCFG def (nts, ts, starts, rules) =
    let mylookup l x = case lookup x l of {Just y -> y; Nothing -> def} in
    (nts, ts, mylookup starts, mylookup rules)

-----------------------------------------------------------
-- Familiar semiring stuff, same as last week

class Semiring a where
    (&&&) :: a -> a -> a
    (|||) :: a -> a -> a
    gtrue :: a
    gfalse :: a

gen_or :: Semiring a => [a] -> a
gen_or list = case list of {[] -> gfalse; (x:xs) -> x ||| (gen_or xs)}

gen_and :: Semiring a => [a] -> a
gen_and list = case list of {[] -> gtrue; (x:xs) -> x &&& (gen_and xs)}

instance Semiring Bool where
    x &&& y = x && y
    x ||| y = x || y
    gtrue = True
    gfalse = False

instance Semiring Double where
    x &&& y = x * y
    x ||| y = x + y
    gtrue = 1.0
    gfalse = 0.0

-----------------------------------------------------------
-- Some example grammars

-- From (12) on the handout
cfg12 :: GenericCFG Cat String Bool
cfg12 = makeGCFG False ([VP,NP,PP,V,P], ["watches","spies","telescopes","with"],
                        [(VP,True)],
                        [(NTRule VP (V,NP), True),   (NTRule NP (NP,PP), True),     (NTRule PP (P,NP), True),
                         (NTRule VP (VP,PP), True),  (TRule NP "telescopes", True),
                         (TRule VP "watches", True), (TRule NP "watches", True),    (TRule P "with", True),
                         (TRule VP "spies", True),   (TRule NP "spies", True),      (TRule V "watches", True)
                        ]
                       )

-- A probabilistic version of cfg12
cfg12a :: GenericCFG Cat String Double
cfg12a = makeGCFG 0.0 ([VP,NP,PP,V,P], ["watches","spies","telescopes","with"],
                       [(VP,1.0)],
                       [(NTRule VP (V,NP), 0.4),   (NTRule NP (NP,PP), 0.2),     (NTRule PP (P,NP), 1.0),
                        (NTRule VP (VP,PP), 0.3),  (TRule NP "telescopes", 0.3),
                        (TRule VP "watches", 0.2), (TRule NP "watches", 0.3),    (TRule P "with", 1.0),
                        (TRule VP "spies", 0.1),   (TRule NP "spies", 0.2),      (TRule V "watches", 1.0)
                       ]
                      )

-- Another probabilistic version of cfg12, with starting probability
-- split evenly between VP and NP
cfg12b :: GenericCFG Cat String Double
cfg12b = makeGCFG 0.0 ([VP,NP,PP,V,P], ["watches","spies","telescopes","with"],
                       [(VP,0.5), (NP,0.5)],
                       [(NTRule VP (V,NP), 0.4),   (NTRule NP (NP,PP), 0.2),     (NTRule PP (P,NP), 1.0),
                        (NTRule VP (VP,PP), 0.3),  (TRule NP "telescopes", 0.3),
                        (TRule VP "watches", 0.2), (TRule NP "watches", 0.3),    (TRule P "with", 1.0),
                        (TRule VP "spies", 0.1),   (TRule NP "spies", 0.2),      (TRule V "watches", 1.0)
                       ]
                      )

-----------------------------------------------------------
-- Functions for inside values

insideBool :: GenericCFG nt t Bool -> [t] -> nt -> Bool
insideBool cfg str n =
    let (nts, ts, i, r) = cfg in
    case str of
    [] -> False
    (x:[]) -> r (TRule n x)
    (x:y:rest2) -> let conj i ld rd = r (NTRule n (ld,rd)) &&
                                        insideBool cfg (take i str) ld &&
                                        insideBool cfg (drop i str) rd
                   in
                   or (liftA3 conj [1 .. (length str - 1)] nts nts)

inside :: (Semiring v) => GenericCFG nt t v -> [t] -> nt -> v
inside cfg str n =
    let (nts, ts, i, r) = cfg in
    case str of
    [] -> gfalse
    (x:[]) -> r (TRule n x)
    (x:y:rest2) -> let conj i ld rd = r (NTRule n (ld,rd)) &&&
                                        inside cfg (take i str) ld &&&
                                        inside cfg (drop i str) rd
                   in
                   gen_or (liftA3 conj [1 .. (length str - 1)] nts nts)

fastInside :: (Ord nt, Ord t, Semiring v) => GenericCFG nt t v -> [t] -> nt -> v
fastInside cfg str n =
    let (nts, ts, i, r) = cfg in
    M.memoFix2
    (\smaller -> \str -> \n ->
        case str of
        [] -> M.lift0 gfalse
        (x:[]) -> M.lift0 (r (TRule n x))
        (_:(_:_)) -> let conjResult i ld rd = M.liftMany gen_and [M.lift0 (r (NTRule n (ld,rd))),
                                                                  smaller (take i str) ld,
                                                                  smaller (drop i str) rd] in
                     M.liftMany gen_or (liftA3 conjResult [1 .. length str - 1] nts nts)
    ) str n

-----------------------------------------------------------
-- This combination of two expressions, where we're very careful we make sure to
-- cover all our cases systematically:
--
--     case str of
--     [] -> ...
--     (x:rest) -> case rest of
--                 [] -> ...
--                 (y:rest2) -> ...
--
-- is equivalent to this shorter version, which is essentially what we're using
-- in the inside functions above:
--
--     case str of
--     [] -> ...
--     (x:[]) -> ...
--     (x:(y:rest2)) -> ...
--
