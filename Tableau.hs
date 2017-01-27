module Tableau where

import CoreLang
import Rules
import Parser (parseL, parseLStat, parseModel')

import Debug.Trace

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.List (intercalate)

import qualified Data.Map as M

debug = flip trace


data RuleThunk = 
    SimpU String URule 
  | SimpB String BRule 
  | Ba
  | NBa

instance Show RuleThunk where
    show = getRuleName

getRuleName :: RuleThunk -> String
getRuleName (SimpU s _) = s
getRuleName (SimpB s _) = s
getRuleName Ba = "ba"
getRuleName NBa = "negBa"


rules = [ 
        (SimpU "and" Rules.and), (SimpU "negNeg" negNeg), 
        (SimpU "arrP" arrP), (SimpU "arrNegP" arrNegP), (SimpU "negBoxM" negBoxM),
        (SimpU "valid" valid), (SimpU "emptyInvalid" emptyInvalid), 
        (SimpU "boxUnion" boxUnion),

        (SimpB "bot" bot), (SimpB "clash" clash), 

        (SimpU "negAnd" negAnd), (SimpU "boxM" boxM), (SimpU "invalid" invalid),
        (SimpU "negBoxUnion" negBoxUnion), 
        Ba, NBa
    ]

getRule :: Set String -> RuleThunk
getRule labs = head $ filter (\x -> not $ getRuleName x `S.member` labs) rules


toTuples :: Ord a => Set a -> [(a,a)]
toTuples s = aux (S.toList s)
    where 
        aux :: [a] -> [(a,a)]
        aux [] = []
        aux (x:xs) = [ (x, y) | y <- xs ] ++ aux xs

applyURule r sΓ = applyRuleA r (S.toList sΓ) sΓ
applyBRule r sΓ = applyRuleA r (toTuples sΓ) sΓ


sat lab = lab == (S.delete "negBa" $ S.fromList (map getRuleName rules)) 

filterNBa :: (Set TTerm) -> (Set TTerm)
filterNBa s = S.filter aux s
    where
        aux :: TTerm -> Bool
        aux (Form _ _ (Neg (B _ _))) = True
        aux _ = False

type Γ = ((Set TTerm) , (Set String) , (Set TTerm))

init :: L -> Γ
init φ = (S.singleton (Form 0 [] φ), S.empty, S.empty)


mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (a , b) = (f a , b)

runTab :: Γ -> Maybe (Set TTerm)
runTab (sΓ, lab, nBa) = trace info $
    if Bot `S.member` sΓ then Nothing `debug` ("closed branch: " ++ sshow sΓ)
    else if sat lab && nBa == (filterNBa sΓ) then Just sΓ `debug` ("open branch: " ++ sshow sΓ ++ "\nlabels: " ++ sshow lab)
    else -- trace ("applying rule " ++ getRuleName (getRule lab) ++ "\n\n") $ 
        case getRule lab of
            SimpU l r -> aux [l] (applyURule r sΓ , S.empty)
            SimpB l r -> aux [l] (applyBRule r sΓ , S.empty)
            Ba -> aux ["ba"] (applyBa (toTuples sΓ) [sΓ] , S.empty)
            NBa -> aux [] $ mapFst (:[]) (applyNBa (S.toList sΓ) sΓ nBa)
    where
        aux l (sΓlst , nBa') = foldMap 
            (\sΓ' -> 
                if sΓ == sΓ' then runTab (sΓ' , ((S.fromList l) `S.union` lab), nBa `S.union` nBa') 
                else runTab (sΓ' , S.empty, nBa `S.union` nBa') `debug` ("successfully applied " ++ (if null l then "nBa" else head l) ++ "\n\n")
            )
            sΓlst -- `debug` ("branches: " ++ intercalate "\n" (map sshow sΓlst))

        info = 
            ("labels:" ++ sshow lab ++ "\n") ++
            ("nBa's:" ++ sshow nBa ++ "\n") ++
            ("Γ: " ++ sshow sΓ ++ "\n") ++
            ("filtered Γ" ++ sshow (filterNBa sΓ) ++ "\n\n")

isValidStat str = do
    case parseLStat str of 
        Just res -> do
            show res
            -- putStr $ sshow $ fst $ Tableau.init res
            return $ runTab $ Tableau.init (Neg res)