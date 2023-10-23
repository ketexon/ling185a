module Assignment02 where
-- Imports everything from the Recursion module.
import Recursion
-- Imports just a few things that we have seen from the standard Prelude module.
-- (If there is no explicit 'import Prelude' line, then the entire Prelude
-- module is imported. I'm restricting things here to a very bare-bones system.)
import Prelude((+), (-), (*), (<), (>), (++), not, (||), (&&), Bool(..), Int, Show, Char, Eq)
------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
-- Write all your code below this line

-- Utility functions for easier writing

add :: Numb -> Numb -> Numb
add x y = case x of
    Z -> y                              -- 0 + y = y
    S x' -> S (Assignment02.add x' y)   -- x + y = 1 + (x - 1) * y

div2 :: Numb -> Numb
div2 x = case x of
    S (S x') -> S (div2 x')         -- x/2 = (x - 2)/2 + 1
    _ -> Z                          -- 1/2 = 0, 0/2 = 0

intToNumb :: Int -> Numb
intToNumb x = case x of
    0 -> Z
    _ -> S(intToNumb (x - 1))

-- 1.A

mult :: Numb -> Numb -> Numb
mult x y = case x of
    Z -> Z                                  -- 0 * y = 0
    S x' -> Assignment02.add y (mult x' y)  -- x * y = y + (x - 1) * y

-- 1.B

sumUpTo :: Numb -> Numb
-- one way to do it is via math (very fast :3)
-- sumUpTo x = div2 (mult x (S x))
-- another way is to use recursion
sumUpTo x = case x of
    Z -> Z
    S x' -> Assignment02.add x (sumUpTo x')

-- 1.C
isEqual :: Numb -> Numb -> Bool
isEqual x y = case (x, y) of
    (S x', S y') -> isEqual x' y'
    (Z, Z) -> True
    _ -> False

-- 1.D
numbToInt :: Numb -> Int
numbToInt x = case x of
    Z -> 0
    S x' -> 1 + numbToInt x'

-- 2.E
count :: (a -> Bool) -> ([a] -> Numb)
count f = \l -> case l of
            [] -> Z
            x:xs -> if f x then S ((count f) xs) else (count f) xs

-- 2.F
addToEnd :: a -> ([a] -> [a])
addToEnd a l = case l of
                [] -> [a]
                x:xs -> x : addToEnd a xs

-- 2.G
remove :: (a -> Bool) -> ([a] -> [a])
remove test = \l -> case l of
                [] -> []
                x:xs -> (if test x then [] else [x]) ++ (remove test) xs

-- 2.H
prefix :: Numb -> ([a] -> [a])
prefix n = case n of
            Z -> \l -> []
            S n' -> \l -> case l of
                [] -> []
                x:xs -> x : (prefix n') xs

-- 2.I
reverse :: [a] -> [a]
reverse l = case l of
    [] -> []
    x:xs -> (reverse xs) ++ [x]

-- 3.J
--data RegExp a =
--      Lit a
--      | Alt (RegExp a) (RegExp a) | Concat (RegExp a) (RegExp a)
--      | Star (RegExp a) | ZeroRE | OneRE
--       deriving (Eq,Show)
countStars :: RegExp a -> Numb
countStars r = case r of
    Alt a b -> Assignment02.add (countStars a) (countStars b)
    Concat a b -> Assignment02.add (countStars a) (countStars b)
    Star a -> S (countStars a)
    _ -> Z

-- 3.K
depth :: RegExp a -> Numb
depth r = case r of
    Alt a b -> S (bigger (depth a) (depth b))
    Concat a b -> S (bigger (depth a) (depth b))
    Star a -> S (depth a)
    _ -> S Z

-- 3.L
reToString :: RegExp Char -> [Char]
reToString re = case re of
    Lit a -> [a]
    ZeroRE -> ['0']
    OneRE -> ['1']
    Alt a b -> "(" ++ reToString a ++ "|" ++ reToString b ++ ")"
    Concat a b -> "(" ++ reToString a ++ "." ++ reToString b ++ ")"
    Star a -> reToString a ++ "*"