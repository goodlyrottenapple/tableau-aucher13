module Rules where

import CoreLang

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map, (!))
import qualified Data.Map as M

-- box :: Model' -> L -> L
-- box m l = Box (M m) l

-- m'1 :: Model'
-- m'1 = Model "w1" r pre
--     where
--         r = addR "w1" "a1" "u1" $ addR "u1" "a1" "u1" $ addR "w1" "a2" "w1" $ addR "u1" "a2" "u1" M.empty
--         pre = M.empty

updateModel :: Map World World -> Model' -> Model'
updateModel r (Model w r' pre) = Model (r ! w) r' pre


type Rule inp = inp -> [Set TTerm]

type URule = Rule TTerm
type BRule = Rule (TTerm , TTerm)
-- type BRuleB = TTerm -> TTerm -> (Set TTerm , Set TTerm)

-- (σ Σ′ φ ∧ ψ)
-- ------------
--   (σ Σ′ φ)
--   (σ Σ′ ψ)
and :: URule
and (Form σ lΣ (φ :^: ψ)) = [S.fromList [(Form σ lΣ φ), (Form σ lΣ ψ)]]
and _ = []


--    (σ Σ′ ¬(φ∧ψ))
-- -------------------
-- (σ Σ′ ¬φ)|(σ Σ′ ¬ψ)
negAnd :: URule
negAnd (Form σ lΣ (Neg (φ :^: ψ))) = [
        S.singleton (Form σ lΣ (Neg φ)), 
        S.singleton (Form σ lΣ (Neg ψ))
    ]
negAnd _ = []

-- (σ Σ′ ¬¬φ)
-- ----------
--  (σ Σ′ φ)
negNeg :: URule
negNeg (Form σ lΣ (Neg (Neg φ))) = [S.singleton (Form σ lΣ φ)]
negNeg _ = []

-- (σ Σ′ p)
-- (σ Σ′ ¬p)
-- ---------
--     ⊥
bot :: BRule
bot ((Form σ lΣ (At p)) , (Form σ' lΣ' (Neg (At p')))) 
    | σ == σ' && lΣ == lΣ' && p == p' = [S.singleton Bot]
    | otherwise = []
bot ((Form σ' lΣ' (Neg (At p'))), (Form σ lΣ (At p))) =
    bot ((Form σ lΣ (At p)), (Form σ' lΣ' (Neg (At p'))))
bot _ = []

-- (σ Σ′ p)
-- --------
-- (σ ε p)
arrP :: URule
arrP (Form σ lΣ (At p)) = [S.singleton (Form σ [] (At p))]
arrP _ = []

-- (σ Σ′ ¬p)
-- ---------
-- (σ ε ¬p)
arrNegP :: URule
arrNegP (Form σ lΣ (Neg (At p))) = [S.singleton (Form σ [] (Neg (At p)))]
arrNegP _ = []

-- (σ Σ′ ¬[M′, w′]φ)
-- -----------------
--  (σ Σ′;M′,w′ OK)
--  (σ Σ′;M′,w′ ¬φ)
negBoxM :: URule
negBoxM (Form σ lΣ (Neg ((M m) :□: φ))) = [S.fromList [
        (Valid σ (m : lΣ)),
        (Form σ (m : lΣ) (Neg φ))
    ]]
negBoxM _ = []

--        (σ Σ′ [M′, w′]φ)
-- --------------------------------
-- (σ Σ′;M′,w′ ⊗) | (σ Σ′;M′,w′ OK)
--                | (σ Σ′;M′,w′ φ)
boxM :: URule
boxM (Form σ lΣ ((M m) :□: φ)) = [
        S.singleton (Invalid σ (m:lΣ)),
        S.fromList [
                (Valid σ (m:lΣ)),
                (Form σ (m:lΣ) φ)
            ]
    ]
boxM _ = []

-- (σ Σ′;M′,w′ OK)
-- ---------------
-- (σ Σ′ Pre(w′))
-- (σ Σ′ OK)
valid :: URule
valid (Valid σ ((Model w r pre):lΣ)) = [S.fromList [
        (Form σ lΣ (pre ! w)),
        (Valid σ lΣ)
    ]]
valid _ = []

--      (σ Σ′;M′,w′ ⊗)
-- --------------------------
-- (σ Σ′ ¬Pre(w′)) | (σ Σ′ ⊗)
-- (σ Σ′ OK)       |
invalid :: URule
invalid (Invalid σ ((Model w r pre):lΣ)) = [
        S.fromList [
                (Form σ lΣ (Neg (pre ! w))),
                (Valid σ lΣ)
            ],
        S.singleton (Invalid σ lΣ)
    ]
invalid _ = []

-- (σ Σ′ ⊗)
-- (σ Σ′ OK)
-- ---------
--     ⊥
clash :: BRule
clash ((Valid σ lΣ) , (Invalid σ' lΣ'))
    | σ == σ' && lΣ == lΣ' = [S.singleton Bot]
    | otherwise = []
clash ((Invalid σ lΣ) , (Valid σ' lΣ')) = 
    clash ((Valid σ' lΣ') , (Invalid σ lΣ))
clash _ = []

-- (σ ε ⊗)
-- -------
--    ⊥
emptyInvalid :: URule
emptyInvalid (Invalid σ []) = [S.singleton Bot]
emptyInvalid _ = []

-- (σ Σ′ [π∪γ]φ)
-- -------------
--  (σ Σ′ [π]φ)
--  (σ Σ′ [γ]φ)
boxUnion :: URule
boxUnion (Form σ lΣ ((π :∪: γ) :□: φ)) = [S.fromList [
        (Form σ lΣ (π :□: φ)),
        (Form σ lΣ (γ :□: φ))
    ]]
boxUnion _ = []

--       (σ Σ′ ¬[π∪γ]φ)
-- ---------------------------
-- (σ Σ′ ¬[π]φ) | (σ Σ′ ¬[γ]φ)
negBoxUnion :: URule
negBoxUnion (Form σ lΣ (Neg ((π :∪: γ) :□: φ))) = [
        S.singleton (Form σ lΣ (Neg (π :□: φ))),
        S.singleton (Form σ lΣ (Neg (γ :□: φ)))
    ]
negBoxUnion _ = []





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
getwRa's agt ms = mapM (getwRa agt) ms

genModelMapList :: Agt -> [Model'] -> Maybe (Set (Map World World))
genModelMapList agt ms = do
    lst <- getwRa's agt ms
    return $ S.fromList $ map M.fromList $ aux2 lst

    where
        aux1 :: (a , [b]) -> [(a , b)]
        aux1 (a , bs) = [ (a, b) | b <- bs ]

        prod :: [a] -> [[a]] -> [[a]]
        prod [] ys = []
        prod (x:xs) ys = [x:y | y <- ys] ++ (prod xs ys)

        aux2 :: [(a , [b])] -> [[(a , b)]]
        aux2 [] = []
        aux2 [x] = map (:[]) $ aux1 x
        aux2 (x:xs) = aux1 x `prod` (aux2 xs)



-- testGenModelMapList fileName ag = do 
--   contents <- readFile fileName

--   -- contents <- hGetContents handle
--   case parseModel' contents of
--     Just res -> do
--         print res
--         print $ getwRa ag $ head (M.elems res)
--         print $ getwRa's ag (M.elems res)
--         print $ genModelMapList ag (M.elems res)
--     Nothing -> print $ genModelMapList "a1" []


-- aggressively try applying the rule r to all TTerms in the set sΓ
applyRuleA :: (Ord a, Show a) => (b -> [Set a]) -> [b] -> Set a -> [Set a]
applyRuleA rule lst sΓ = S.toList $ S.fromList $ foldr 
 ( \tterm lst -> (rule tterm) `unionMap` lst )--`debug` (sshow $ S.fromList (rule tterm)) ) 
 [sΓ] lst


-- aggressively try applying the Ba rule to all TTerms in the set sΓ

--                (σ M′1,w1′;...;M′i,wi′ Baφ)
--                (σ Ra σ1)
-- --------------------------------------------------------
-- (σ1 M′1,u′1;...;M′i,u′i OK) | (σ1 M′1,u′1;...;M′i,u′i ⊗)
-- (σ1 M′1,u′1;...;M′i,u′i φ)  |
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


-- (σ M′1,w1′;...;M′i,wi′ ¬Baφ)
-- ----------------------------
-- (σ Ra σnew)
-- (σnew M′1,u′1;...;M′i,u′i OK)
-- (σnew M′1,u′1;...;M′i,u′i ¬φ)
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


