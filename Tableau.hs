module Tableau where

import CoreLang
import Rules
import Parser (parseL, parseLStat)

import Debug.Trace

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.List (intercalate)


debug = flip trace


-- data TTree t l = Leaf (Set t) | Node (Set t) l t [TTree t l]

type Γ = ((Set TTerm) , (Set String))

toTuples :: Ord a => Set a -> [(a,a)]
toTuples s = aux (S.toList s)
    where 
        aux :: [a] -> [(a,a)]
        aux [] = []
        aux (x:xs) = [ (x, y) | y <- xs ] ++ aux xs


unMap :: Ord a => [Set a] -> [Set a] -> [Set a]
unMap [] s = s
unMap s [] = []
unMap s (x:xs) = map (S.union x) s ++ (unMap s xs)

-- aggresively try aplying the rule r to all TTerms in the set Γ
applyRuleA :: (Ord a, Show a) => (b -> [Set a]) -> [b] -> Set a -> [Set a]
applyRuleA rule lst sΓ = S.toList $ S.fromList $ foldr 
 (\tterm lst -> (rule tterm) `unMap` lst )--`debug` (sshow $ S.fromList (rule tterm)) ) 
 [sΓ] lst

applyURule r sΓ = applyRuleA r (S.toList sΓ) sΓ
applyBRule r sΓ = applyRuleA r (toTuples sΓ) sΓ

-- sat :: Set TTerm -> Set TTerm -> Bool
-- sat orig new = orig == new || Bot `S.member` new

data RuleThunk = 
    SimpU String URule 
  | SimpB String BRule 
  | Ba (Map World World)
  | NBa (Map World World)

instance Show RuleThunk where
    show = getRuleName

getRuleName :: RuleThunk -> String
getRuleName (SimpU s _) = s
getRuleName (SimpB s _) = s
getRuleName (Ba _) = "ba"
getRuleName (NBa _) = "negBa"


-- gamma = S.fromList [ "x" , "y" ]
-- r1 s = [S.singleton ('a':s), S.singleton ('a':s)]


rules = [ 
        (SimpU "and" Rules.and), (SimpU "negNeg" negNeg), 
        (SimpU "arrP" arrP), (SimpU "arrNegP" arrNegP), (SimpU "negBoxM" negBoxM),
        (SimpU "valid" valid), (SimpU "emptyInvalid" emptyInvalid), 
        (SimpU "boxUnion" boxUnion),

        (SimpB "bot" bot), (SimpB "clash" clash), 

        (SimpU "negAnd" negAnd), (SimpU "boxM" boxM), (SimpU "invalid" invalid),
        (SimpU "negBoxUnion" negBoxUnion)
    ]

getRule :: Set String -> RuleThunk
getRule labs = head $ filter (\x -> not $ getRuleName x `S.member` labs) rules


sat lab = lab == S.fromList (map getRuleName rules)

init :: L -> Γ
init φ = (S.singleton (Form 0 [] φ), S.empty)

runTab :: Γ -> Maybe (Set TTerm)
runTab (sΓ, lab) = trace ("labels:" ++ sshow lab ++ "\n") $
    if Bot `S.member` sΓ then Nothing `debug` ("closed branch: " ++ sshow sΓ)
    else if sat lab then Just sΓ `debug` ("open branch: " ++ sshow sΓ ++ "\nlabels: " ++ sshow lab)
    else -- trace ("applying rule " ++ getRuleName (getRule lab) ++ "\n\n") $ 
        case getRule lab of
            SimpU l r -> aux l (applyURule r sΓ)
            SimpB l r -> aux l (applyBRule r sΓ)
    where
        -- aux l [sΓ'] | sΓ == sΓ' = runTab (sΓ , S.insert l lab) -- `debug` ("rule (" ++ l ++ ") not applicable, adding to label set and trying again with: "++ sshow sΓ)
        --             | otherwise = runTab (sΓ' , S.empty)  -- `debug` ("rule (" ++ l ++ ") applied, new set is: "++ sshow sΓ')
        aux l sΓlst = 
            foldMap 
                (\sΓ' -> 
                    if sΓ == sΓ' then runTab (sΓ' , S.insert l lab) 
                    else runTab (sΓ' , S.empty) `debug` ("succesfully applied " ++ l ++ "\n\n")
                )

                sΓlst `debug` ("branches: " ++ intercalate "\n" (map sshow sΓlst))

isValidStat str = do
    case parseLStat str of 
        Just res -> do
            putStr $ sshow $ fst $ Tableau.init res
            return $ runTab $ Tableau.init (Neg res)