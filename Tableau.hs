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


-- data TTree t l = Leaf (Set t) | Node (Set t) l t [TTree t l]

type Γ = ((Set TTerm) , (Set String))

toTuples :: Ord a => Set a -> [(a,a)]
toTuples s = aux (S.toList s)
    where 
        aux :: [a] -> [(a,a)]
        aux [] = []
        aux (x:xs) = [ (x, y) | y <- xs ] ++ aux xs


unionMap :: Ord a => [Set a] -> [Set a] -> [Set a]
unionMap [] s = s
unionMap s [] = []
unionMap s (x:xs) = map (S.union x) s ++ (unionMap s xs)


getwRa :: Agt -> Model' -> Maybe (World, [World])
getwRa agt (Model w r _) = do
    ra <- M.lookup agt r
    let us = [u | (w' , u) <- S.toList ra, w == w'] in
        if null us then Nothing else return (w , us)

getwRa's :: Agt -> [Model'] -> Maybe [(World, [World])]
getwRa's agt [] = Just []
getwRa's agt ms = mapM (getwRa agt) ms

aux1 :: (a , [b]) -> [(a , b)]
aux1 (a , bs) = [ (a, b) | b <- bs ]

prod :: [a] -> [[a]] -> [[a]]
prod [] ys = []
prod (x:xs) ys = [x:y | y <- ys] ++ (prod xs ys)

aux2 :: [(a , [b])] -> [[(a , b)]]
aux2 [] = []
aux2 [x] = map (:[]) $ aux1 x
aux2 (x:xs) = aux1 x `prod` (aux2 xs)

genModelMapList :: Agt -> [Model'] -> Maybe (Set (Map World World))
genModelMapList agt ms = do
    lst <- getwRa's agt ms
    return $ S.fromList $ map M.fromList $ aux2 lst


testGenModelMapList fileName ag = do 
  contents <- readFile fileName

  -- contents <- hGetContents handle
  case parseModel' contents of
    Just res -> do
        print res
        print $ getwRa ag $ head (M.elems res)
        print $ getwRa's ag (M.elems res)
        print $ genModelMapList ag (M.elems res)
    Nothing -> print $ genModelMapList "a1" []


-- aggresively try aplying the rule r to all TTerms in the set Γ
applyRuleA :: (Ord a, Show a) => (b -> [Set a]) -> [b] -> Set a -> [Set a]
applyRuleA rule lst sΓ = S.toList $ S.fromList $ foldr 
 ( \tterm lst -> (rule tterm) `unionMap` lst )--`debug` (sshow $ S.fromList (rule tterm)) ) 
 [sΓ] lst

applyURule r sΓ = applyRuleA r (S.toList sΓ) sΓ
applyBRule r sΓ = applyRuleA r (toTuples sΓ) sΓ


applyBa :: [(TTerm, TTerm)] -> [Set TTerm] -> [Set TTerm]
applyBa [] sΓ = sΓ
applyBa ((((Form σ [] (B a φ)) , (R σ' a' σ1))):xs) sΓ 
    | σ == σ' && a == a' = applyBa xs $ [
        S.fromList [
                (Valid σ1 []),
                (Form σ1 [] φ)
            ],
        S.singleton (Invalid σ1 [])
    ] `unionMap` sΓ
    | otherwise = applyBa xs sΓ

applyBa ((((Form σ lΣ (B a φ)) , (R σ' a' σ1))):xs) sΓ 
    | σ == σ' && a == a' = case genModelMapList a lΣ of
    Just sΔ -> applyBa xs $ foldr
        ( \δ sΓ' -> let δΣ = map (updateModel δ) lΣ in
            [
                S.fromList [
                        (Valid σ1 δΣ),
                        (Form σ1 δΣ φ)
                    ],
                S.singleton (Invalid σ1 δΣ)
            ] `unionMap` sΓ'
        )
        sΓ (S.toList sΔ) 
            -- ( \m lst -> (ba m (((Form σ lΣ (B a φ)) , (R σ' a' σ1)))) `unionMap` lst )--`debug` (sshow $ S.fromList (rule tterm)) ) 
            -- sΓ (S.toList mapSet)
    Nothing -> applyBa xs sΓ
    | otherwise = applyBa xs sΓ
applyBa ((((R σ' a' σ1) , (Form σ lΣ (B a φ)))):xs) sΓ = 
        applyBa ((((Form σ lΣ (B a φ)) , (R σ' a' σ1))):xs) sΓ
applyBa (_:xs) sΓ = applyBa xs sΓ


newLab :: Set TTerm -> Lab
newLab set = (biggestLab (S.toList set) 0) + 1
    where
        biggestLab [] acc = acc
        biggestLab ((Form l _ _):xs) acc | l > acc = biggestLab xs l
                                         | otherwise = biggestLab xs acc
        biggestLab (_:xs) acc = biggestLab xs acc                                   


applyNBa :: [TTerm] -> Set TTerm -> Set TTerm
applyNBa [] sΓ = sΓ
applyNBa ( (Form σ [] (Neg (B a φ))) : xs ) sΓ = applyNBa xs $
    S.fromList [
        (R σ a σNew),
        (Valid σNew []),
        (Form σNew [] (Neg φ))
    ] `S.union` sΓ

    where σNew = newLab sΓ
applyNBa ( (Form σ lΣ (Neg (B a φ))) : xs ) sΓ = case genModelMapList a lΣ of
    Just sΔ -> applyNBa xs $ foldr 
        ( \δ sΓ' -> let 
                σNew = newLab sΓ'
                δΣ = map (updateModel δ) lΣ
            in
            S.fromList [
                (R σ a σNew),
                (Valid σNew δΣ),
                (Form σNew δΣ (Neg φ))
            ] `S.union` sΓ'
        )
        sΓ (S.toList sΔ)
    Nothing -> applyNBa xs sΓ
applyNBa (_:xs) sΓ = applyNBa xs sΓ



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
            Ba -> aux "ba" (applyBa (toTuples sΓ) [sΓ])
            NBa -> aux "negBa" [applyNBa (S.toList sΓ) sΓ]
    where
        aux l sΓlst = foldMap 
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