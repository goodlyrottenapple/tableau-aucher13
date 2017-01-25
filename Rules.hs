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


type URule = TTerm -> Set TTerm
type BRule = TTerm -> TTerm -> Set TTerm
type URuleB = TTerm -> (Set TTerm , Set TTerm)
type BRuleB = TTerm -> TTerm -> (Set TTerm , Set TTerm)

-- (σ Σ′ φ ∧ ψ)
-- ------------
--   (σ Σ′ φ)
--   (σ Σ′ ψ)
and :: URule
and (Form σ lΣ (φ :&: ψ)) = S.fromList [(Form σ lΣ φ), (Form σ lΣ ψ)]
and _ = S.empty

--    (σ Σ′ ¬(φ∧ψ))
-- -------------------
-- (σ Σ′ ¬φ)|(σ Σ′ ¬ψ)
negAnd :: URuleB
negAnd (Form σ lΣ (Neg (φ :&: ψ))) = (
        S.singleton (Form σ lΣ (Neg φ)), 
        S.singleton (Form σ lΣ (Neg ψ))
    )
negAnd _ = (S.empty, S.empty)

-- (σ Σ′ ¬¬φ)
-- ----------
--  (σ Σ′ φ)
negNeg :: URule
negNeg (Form σ lΣ (Neg (Neg φ))) = S.singleton (Form σ lΣ φ)
negNeg _ = S.empty

-- (σ Σ′ p)
-- (σ Σ′ ¬p)
-- ---------
--     ⊥
bot :: BRule
bot (Form σ lΣ (At p)) (Form σ' lΣ' (Neg (At p'))) 
    | σ == σ' && lΣ == lΣ' && p == p' = S.singleton Bot
    | otherwise = S.empty
bot (Form σ' lΣ' (Neg (At p'))) (Form σ lΣ (At p)) =
    bot (Form σ lΣ (At p)) (Form σ' lΣ' (Neg (At p')))
bot _ _ = S.empty

-- (σ Σ′ p)
-- --------
-- (σ ε p)
arrP :: URule
arrP (Form σ lΣ (At p)) = S.singleton (Form σ [] (At p))
arrP _ = S.empty

-- (σ Σ′ ¬p)
-- ---------
-- (σ ε ¬p)
arrNegP :: URule
arrNegP (Form σ lΣ (Neg (At p))) = S.singleton (Form σ [] (Neg (At p)))
arrNegP _ = S.empty

--                (σ M′1,w1′;...;M′i,wi′ Baφ)
--                (σ Ra σ1)
-- --------------------------------------------------------
-- (σ1 M′1,u′1;...;M′i,u′i OK) | (σ1 M′1,u′1;...;M′i,u′i ⊗)
-- (σ1 M′1,u′1;...;M′i,u′i φ)  |
ba :: Map World World -> BRuleB
ba r (Form σ lΣ (B a φ)) (R σ' a' σ1)
    | σ == σ' && a == a' = (
        S.fromList [
                (Valid σ1 (map (updateModel r) lΣ)),
                (Form σ1 (map (updateModel r) lΣ) φ)
            ],
        S.singleton (Invalid σ1 (map (updateModel r) lΣ))
    )
    | otherwise = (S.empty, S.empty)
ba r (R σ' a' σ1) (Form σ lΣ (B a φ)) = 
    ba r (Form σ lΣ (B a φ)) (R σ' a' σ1)
ba _ _ _ = (S.empty, S.empty)

-- (σ M′1,w1′;...;M′i,wi′ ¬Baφ)
-- ----------------------------
-- (σ Ra σnew)
-- (σnew M′1,u′1;...;M′i,u′i OK)
-- (σnew M′1,u′1;...;M′i,u′i ¬φ)
negBa :: Map World World -> Lab -> URule
negBa r σNew (Form σ lΣ (Neg (B a φ))) = S.fromList [
        (R σ a σNew),
        (Valid σNew (map (updateModel r) lΣ)),
        (Form σNew (map (updateModel r) lΣ) (Neg φ))
    ]
negBa _ _ _ = S.empty

-- (σ Σ′ ¬[M′, w′]φ)
-- -----------------
--  (σ Σ′;M′,w′ OK)
--  (σ Σ′;M′,w′ ¬φ)
negBoxM :: URule
negBoxM (Form σ lΣ (Neg ((M m) :□: φ))) = S.fromList [
        (Valid σ (m : lΣ)),
        (Form σ (m : lΣ) (Neg φ))
    ]
negBoxM _ = S.empty

--        (σ Σ′ [M′, w′]φ)
-- --------------------------------
-- (σ Σ′;M′,w′ ⊗) | (σ Σ′;M′,w′ OK)
--                | (σ Σ′;M′,w′ φ)
boxM :: URuleB
boxM (Form σ lΣ ((M m) :□: φ)) = (
        S.singleton (Invalid σ (m:lΣ)),
        S.fromList [
                (Valid σ (m:lΣ)),
                (Form σ (m:lΣ) φ)
            ]
    )
boxM _ = (S.empty, S.empty)

-- (σ Σ′;M′,w′ OK)
-- ---------------
-- (σ Σ′ Pre(w′))
-- (σ Σ′ OK)
valid :: URule
valid (Valid σ ((Model w r pre):lΣ)) = S.fromList [
        (Form σ lΣ (pre ! w)),
        (Valid σ lΣ)
    ]
valid _ = S.empty

--      (σ Σ′;M′,w′ ⊗)
-- --------------------------
-- (σ Σ′ ¬Pre(w′)) | (σ Σ′ ⊗)
-- (σ Σ′ OK)       |
invalid :: URuleB
invalid (Invalid σ ((Model w r pre):lΣ)) = (
        S.fromList [
                (Form σ lΣ (Neg (pre ! w))),
                (Valid σ lΣ)
            ],
        S.singleton (Invalid σ lΣ)
    )
invalid _ = (S.empty, S.empty)

-- (σ Σ′ ⊗)
-- (σ Σ′ OK)
-- ---------
--     ⊥
clash :: BRule
clash (Valid σ lΣ) (Invalid σ' lΣ') 
    | σ == σ' && lΣ == lΣ' = S.singleton Bot
    | otherwise = S.empty
clash (Invalid σ lΣ) (Valid σ' lΣ') = 
    clash (Valid σ' lΣ') (Invalid σ lΣ)
clash _ _ = S.empty

-- (σ ε ⊗)
-- -------
--    ⊥
emptyInvalid :: URule
emptyInvalid (Invalid σ []) = S.singleton Bot
emptyInvalid _ = S.empty

-- (σ Σ′ [π∪γ]φ)
-- -------------
--  (σ Σ′ [π]φ)
--  (σ Σ′ [γ]φ)
boxUnion :: URule
boxUnion (Form σ lΣ ((π :∪: γ) :□: φ)) = S.fromList [
        (Form σ lΣ (π :□: φ)),
        (Form σ lΣ (γ :□: φ))
    ]
boxUnion _ = S.empty

--       (σ Σ′ ¬[π∪γ]φ)
-- ---------------------------
-- (σ Σ′ ¬[π]φ) | (σ Σ′ ¬[γ]φ)
negBoxUnion :: URuleB
negBoxUnion (Form σ lΣ (Neg ((π :∪: γ) :□: φ))) = (
        S.singleton (Form σ lΣ (Neg (π :□: φ))),
        S.singleton (Form σ lΣ (Neg (γ :□: φ)))
    )