module FinalProject01 where

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List

import CFGParsing


bottomUp :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
bottomUp cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([], input) in
  let goalConfig = ([NoBar start], []) in
  parser [shift, reduce] rules startingConfig goalConfig
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- These functions are placeholders to work with 'bottomUp' in Part 1.3.
-- You should replace 'undefined' in these functions with your own code.

-- REDEFININITION OF HASKELL BUILT IN FUNCTIONS

-- takes a list and returns Nothing if empty or Just the first element of the list
listToMaybe :: [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x:xs) = Just x

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just a) = [a]

-- takes a list of maybes and returns a list of the Just elements
catMaybes :: [Maybe a] -> [a]
catMaybes [] = []
catMaybes (x:xs) = case x of
    Just y -> y:(catMaybes xs)
    Nothing -> catMaybes xs


minNTLength :: (Eq nt, Eq t) => [RewriteRule nt t] -> nt -> Maybe Int
minNTLength rules nt
    = case filteredRules of
        [] -> Nothing
        rules -> Nothing -- foldr1 $ (catMaybes $ )
    where
        -- only select rules whose LHS is nt and that are
        -- not recursive
        ruleFilter (NTRule ruleNT children)
            = ruleNT == nt && not (elem nt children)
        filteredRules = ruleFilter `filter` rules
        getNTRuleChildren (NTRule _ children) = children
        test = ((map minNTLength) . getNTRuleChildren) `map` rules

-- 1.1 A
isRuleCNF :: RewriteRule nt t -> Bool
isRuleCNF (NTRule _  [_, _]) = True
isRuleCNF (TRule _ _) = True
isRuleCNF NoRule = True
isRuleCNF _ = False

-- 1.1 B
isCNF :: CFG nt t -> Bool
isCNF (_, _, _, rules) = and $ map isRuleCNF rules

-- 1.2
pathsToGoalFSA :: (Eq st, Eq sy) =>
    ((st,[sy]), [(st,[sy])]) -> [(st,sy,st)] ->
    [(st,[sy])] -> [[(st,[sy])]]

pathsToGoalFSA (current, history) rules goals
    = if current `elem` goals
        then [history ++ [current]]
        else foldr (++) [] ((\newState -> pathsToGoalFSA (newState, history ++ [current]) rules goals) <$> possibleConsumptions)
    where
        possibleConsumptions = consumeFSA rules current

isNTRule :: RewriteRule nt t -> Bool
isNTRule (NTRule _ _) = True
isNTRule _ = False

-- returns the nt for a terminal t such that TRule nt t is in the rules
findNTsGeneratingT :: (Eq nt, Eq t) => [RewriteRule nt t] -> t -> [nt]
findNTsGeneratingT rules terminal
    = catMaybes (getNT <$> rules)
    where
        getNT (TRule nt t) = if t == terminal then Just nt else Nothing
        getNT _ = Nothing

-- 1.3 C

shift :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shift rules (stack, terminal:syms)
    = ntToParseStep <$> nts
    where
        nts = findNTsGeneratingT rules terminal
        ntToParseStep nt
            = ParseStep
                Shift
                (TRule nt terminal)
                (stack ++ [NoBar nt], syms) -- append to stack
shift _ (_, []) = []

reduce :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
reduce rules (stack, str)
    =  catMaybes $ map tryApplyNTRule rules
    where
        stackLength = length stack
        tryApplyNTRule (NTRule nt children)
            = if stackLength >= childrenLength && drop (stackLength - childrenLength) stack == map NoBar children
                then Just (ParseStep
                    Reduce
                    (NTRule nt children)
                    (take (stackLength - childrenLength) stack ++ [NoBar nt], str)
                )
                else Nothing
            where
                childrenLength = length children
        tryApplyNTRule _ = Nothing

finiteReduce :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
finiteReduce rules config
    = filter parseStepFilter steps
    where
        steps = reduce rules config
        -- filter out rules of the form A -> epsilon
        parseStepFilter (ParseStep _ (NTRule _ []) _) = False
        parseStepFilter _ = True

finiteBottomUp :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
finiteBottomUp (nts, ts, start, rules) input
    = parser [shift, finiteReduce] rules startingConfig goalConfig
    where
        startingConfig = ([], input)
        goalConfig = ([NoBar start], [])


-- 1.3 D

parser :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> [[ParseStep nt t]]  -- List of possible parses.
parser transitions rules startConfig goalConfig
    = foldr (++) [] $ map continueStep steps
    where
        steps = foldr (++) [] $ (\t -> t rules startConfig) <$> transitions
        continueStep step
            = if newConfig == goalConfig
                then [[step]]
                else (step:) <$> parser transitions rules newConfig goalConfig
            where
                ParseStep transition rule newConfig = step

parserStep transitions rules startConfig goalConfig
    = steps
    where
        steps = foldr (++) [] $ (\t -> t rules startConfig) <$> transitions
        continueStep step
            = if newConfig == goalConfig
                then [[step]]
                else (step:) <$> parser transitions rules newConfig goalConfig
            where
                ParseStep transition rule newConfig = step


-- 1.3 E
predict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predict rules (nt:nts, str)
    -- if the current stack is larger than str,
    -- then it cannot be valid, since each nonterminal
    -- eventually produces at least 1 terminal node
    = if 1 + length nts > length str
        then []
        else ruleToParseStep <$> filteredRules
    where
        ruleFilter (NTRule p _) = nt == NoBar p
        ruleFilter _ = False
        -- rules whose lhs is p and RHS is a nonterminal
        filteredRules = filter ruleFilter rules
        ruleToParseStep rule
            = ParseStep Predict rule
                ((NoBar <$> children) ++ nts, str)
            where
                (NTRule p children) = rule
-- can't predict if there's no symbol on stack
predict _ ([], _) = []

match :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
match rules (nt:nts, sym:syms)
    = case find ((==nt) . NoBar) $ findNTsGeneratingT rules sym of
        Just nt -> [ParseStep Match (TRule nt sym) (nts, syms)]
        Nothing -> []
-- Cant match if there's empty stack or empty string
match rules _ = []

topDown :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
topDown (nts, ts, start, rules) input
    = parser [match, predict] rules startingConfig goalConfig
    where
        startingConfig = ([NoBar start], input)
        goalConfig = ([], [])

-- 1.3 F
-- same as shift but prepend to stack
lcShift :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
lcShift rules (stack, terminal:syms)
    = ntToParseStep <$> nts
    where
        nts = findNTsGeneratingT rules terminal
        ntToParseStep nt
            = ParseStep
                Shift
                (TRule nt terminal)
                ((NoBar nt):stack, syms) -- append to stack
lcShift _ (_, []) = []

-- same as match but require stack top to be barred
lcMatch :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
lcMatch rules (nt:nts, sym:syms)
    = case find ((==nt) . Bar) $ findNTsGeneratingT rules sym of
        Just nt -> [ParseStep Match (TRule nt sym) (nts, syms)]
        Nothing -> []
-- Cant match if there's empty stack or empty string
lcMatch rules _ = []


lcPredict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
lcPredict rules (nt:nts, str)
    = ruleToParseStep <$> filteredRules
    where
        ruleFilter (NTRule p (child:children)) = nt == NoBar child
        ruleFilter _ = False
        -- rules whose lhs is p and RHS is a nonterminal
        filteredRules = filter ruleFilter rules
        ruleToParseStep rule
            = ParseStep Predict rule
                ((Bar <$> (drop 1 children)) ++ (NoBar p):nts, str)
            where
                (NTRule p children) = rule
-- can't predict if there's no symbol on stack
lcPredict _ ([], _) = []

lcConnect :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
lcConnect rules (nt1:nt2:nts, str)
    = ruleToParseStep <$> filteredRules
    where
        ruleFilter (NTRule p (child:children)) = nt2 == Bar p && nt1 == NoBar child
        ruleFilter _ = False
        -- rules whose lhs is p and RHS is a nonterminal
        filteredRules = filter ruleFilter rules
        ruleToParseStep rule
            = ParseStep Connect rule
                ((Bar <$> (drop 1 children)) ++ nts, str)
            where
                (NTRule p children) = rule
-- cant connect if there's not two symbols on stack
lcConnect _ _ = []

leftCorner :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
leftCorner (nts, ts, start, rules) input
    = parser [lcShift, lcPredict, lcMatch, lcConnect] rules startingConfig goalConfig
    where
        startingConfig = ([Bar start], input)
        goalConfig = ([], [])

data AB = AB_S | AB_A | AB_B deriving (Eq, Show)

-- L(G) = { ww^R : w \in {a, b}* }
cfgRev :: CFG AB Char
cfgRev
    = (
        [AB_S, AB_A, AB_B],
        ['a', 'b'],
        AB_S,
        [
            NTRule AB_S [AB_A, AB_S, AB_A],
            NTRule AB_S [AB_B, AB_S, AB_B],
            NTRule AB_S [],
            TRule AB_A 'a', TRule AB_B 'b'
        ]
    )