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
    Just y -> y:catMaybes xs
    Nothing -> catMaybes xs

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f [] = []
mapMaybe f (x:xs) = case f x of
    Just y -> y:mapMaybe f xs
    Nothing -> mapMaybe f xs

unwrapStack :: Stack a -> a
unwrapStack (Bar a) = a
unwrapStack (NoBar a) = a

minNTLength :: (Eq nt, Eq t) => [RewriteRule nt t] -> nt -> Int
minNTLength rules nt
    = minimum $ recurse `map` filteredRules
    where
        -- only select rules whose LHS is nt and that are
        -- not recursive
        ruleFilter (NTRule ruleNT children)
            = ruleNT == nt && notElem nt children
        ruleFilter (TRule ruleNT _) = ruleNT == nt
        filteredRules = ruleFilter `filter` rules
        recurse (NTRule _ children) = sum $ minNTLength rules `map` children
        recurse (TRule _ _) = 1
        recurse NoRule = 0

minNTStackLength :: (Eq nt, Eq t) => [RewriteRule nt t] -> Stack nt -> Int
minNTStackLength rules = minNTLength rules . unwrapStack

-- 1.1 A
isRuleCNF :: RewriteRule nt t -> Bool
isRuleCNF (NTRule _  [_, _]) = True
isRuleCNF (TRule _ _) = True
isRuleCNF NoRule = True
isRuleCNF _ = False

-- 1.1 B
isCNF :: CFG nt t -> Bool
isCNF (_, _, _, rules) = all isRuleCNF rules

-- 1.2
pathsToGoalFSA :: (Eq st, Eq sy) =>
    ((st,[sy]), [(st,[sy])]) -> [(st,sy,st)] ->
    [(st,[sy])] -> [[(st,[sy])]]

pathsToGoalFSA (current, history) rules goals
    = if current `elem` goals
        then [history ++ [current]]
        else concatMap (\newState -> pathsToGoalFSA (newState, history ++ [current]) rules goals) possibleConsumptions
    where
        possibleConsumptions = consumeFSA rules current

isNTRule :: RewriteRule nt t -> Bool
isNTRule (NTRule _ _) = True
isNTRule _ = False

-- returns the nt for a terminal t such that TRule nt t is in the rules
findNTsGeneratingT :: (Eq nt, Eq t) => [RewriteRule nt t] -> t -> [nt]
findNTsGeneratingT rules terminal
    = mapMaybe getNT rules
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
    =  mapMaybe tryApplyNTRule rules
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
parserInternal :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> [[ParseStep nt t]]  -- List of possible parses.
parserInternal transitions rules startConfig goalConfig
    = concatMap continueStep steps
    where
        -- [ParseStep SHIFT ... NewConfig]
        results = concatMap (\t -> t rules startConfig) transitions
        steps = concatMap (\t -> t rules startConfig) transitions
        continueStep step
            = if newConfig == goalConfig
                then [[step]]
                else (step:) `map` parserInternal transitions rules newConfig goalConfig
            where
                ParseStep transition rule newConfig = step


parser :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> [[ParseStep nt t]]  -- List of possible parses.
parser transitions rules startConfig goalConfig
    = (ParseStep NoTransition NoRule startConfig:) `map` parserInternal transitions rules startConfig goalConfig


parserStep transitions rules startConfig goalConfig
    = steps
    where
        steps = concatMap (\t -> t rules startConfig) transitions
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
    = if minNTStackLength rules nt + sum (minNTStackLength rules `map` nts) > length str
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

finitePredict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
finitePredict rules (nt:nts, str)
    -- if the current stack is larger than str,
    -- then it cannot be valid, since each nonterminal
    -- eventually produces at least 1 terminal node
    = if minNTStackLength rules nt + sum (minNTStackLength rules `map` nts) > length str
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
finitePredict _ ([], _) = []

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
shiftLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shiftLC rules (stack, terminal:syms)
    = ntToParseStep <$> nts
    where
        nts = findNTsGeneratingT rules terminal
        ntToParseStep nt
            = ParseStep
                Shift
                (TRule nt terminal)
                (NoBar nt:stack, syms) -- append to stack
shiftLC _ (_, []) = []

-- same as match but require stack top to be barred
matchLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
matchLC rules (nt:nts, sym:syms)
    = case find ((==nt) . Bar) $ findNTsGeneratingT rules sym of
        Just nt -> [ParseStep Match (TRule nt sym) (nts, syms)]
        Nothing -> []
-- Cant match if there's empty stack or empty string
matchLC rules _ = []


predictLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predictLC rules (nt:nts, str)
    = ruleToParseStep <$> filteredRules
    where
        ruleFilter (NTRule p (child:children)) = nt == NoBar child
        ruleFilter _ = False
        -- rules whose lhs is p and RHS is a nonterminal
        filteredRules = filter ruleFilter rules
        ruleToParseStep rule
            = ParseStep Predict rule
                ((Bar <$> drop 1 children) ++ NoBar p:nts, str)
            where
                (NTRule p children) = rule
-- can't predict if there's no symbol on stack
predictLC _ ([], _) = []

connectLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
connectLC rules (nt1:nt2:nts, str)
    = ruleToParseStep <$> filteredRules
    where
        ruleFilter (NTRule p (child:children)) = nt2 == Bar p && nt1 == NoBar child
        ruleFilter _ = False
        -- rules whose lhs is p and RHS is a nonterminal
        filteredRules = filter ruleFilter rules
        ruleToParseStep rule
            = ParseStep Connect rule
                ((Bar <$> drop 1 children) ++ nts, str)
            where
                (NTRule p children) = rule
-- cant connect if there's not two symbols on stack
connectLC _ _ = []

leftCorner :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
leftCorner (nts, ts, start, rules) input
    = parser [shiftLC, predictLC, matchLC, connectLC] rules startingConfig goalConfig
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

-- L(G) = { ww^R : w \in {a, b}* }
cfgInf :: CFG AB Char
cfgInf
    = (
        [AB_S],
        ['a'],
        AB_S,
        [
            NTRule AB_S [AB_S], TRule AB_S 'a'
        ]
    )


test = minNTLength rules
    where
        (_, _, _, rules) = cfg12