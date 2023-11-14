{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}
{-# LANGUAGE FlexibleInstances #-}

module Assignment06 where

import Control.Applicative(liftA, liftA2, liftA3)

import ContextFree

data Tree nt t = Leaf nt t | NonLeaf nt (Tree nt t) (Tree nt t) deriving Show

tree1 :: Tree Cat String
tree1 = NonLeaf VP (NonLeaf VP (Leaf V "watches") (Leaf NP "spies"))
                   (NonLeaf PP (Leaf P "with") (Leaf NP "telescopes"))

tree2 :: Tree Cat String
tree2 = NonLeaf VP (Leaf V "watches")
                   (NonLeaf NP (Leaf NP "spies") (NonLeaf PP (Leaf P "with") (Leaf NP "telescopes")))
------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

cartesian2 :: [a] -> [b] -> [(a, b)]
cartesian2 l r = (,) <$> l <*> r

cartesian3 :: [a] -> [b] -> [c] -> [(a, b, c)]
cartesian3 l m r = (,,) <$> l <*> m <*> r

getNT :: Tree nt t -> nt
getNT (Leaf nt _) = nt
getNT (NonLeaf nt _ _) = nt

-- 1A
leftmost :: Tree nt t -> [RewriteRule nt t]
leftmost (Leaf nt t) = [TRule nt t]
leftmost (NonLeaf nt l r) = [NTRule nt (getNT l, getNT r)] ++ leftmost l ++ leftmost r

-- 2B
f :: (Ord nt, Ord t, Semiring a) => GenericCFG nt t a -> [t] -> a
f cfg str
    = gen_or $ (\nt -> initial nt &&& fastInside cfg str nt) <$> nts
    where
        (nts, _, initial, _) = cfg

-- 2C
outside :: (Ord nt, Ord t, Semiring v)
            => GenericCFG nt t v
                -> ([t],[t]) -> nt -> v
outside (_, _, initial, _) ([], []) nt = initial nt
outside cfg (l_str, r_str) nt
    =
        (gen_or
            $ (\(i, p_nt, r_nt) ->
                outside cfg (l_str, drop i r_str) p_nt
                &&& (rule $ NTRule p_nt (nt, r_nt))
                &&& fastInside cfg (take i r_str) r_nt
            ) <$> cartesian3 [1..r_len] nts nts)
        ||| (gen_or
            $ (\(i, p_nt, l_nt) ->
                outside cfg (take i l_str, r_str) p_nt
                &&& (rule $ NTRule p_nt (l_nt, nt))
                &&& fastInside cfg (drop i l_str) l_nt
            ) <$> cartesian3 [0..l_len - 1] nts nts)
    where
        (nts, _, initial, rule) = cfg
        l_len = length l_str
        r_len = length r_str
