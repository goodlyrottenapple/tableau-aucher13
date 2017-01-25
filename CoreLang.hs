{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}

module CoreLang where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map, (!))
import qualified Data.Map as M


data LDynA model = M model | (LDynA model) :∪: (LDynA model) deriving (Eq, Ord)

data LStatA atm agt ldyn = 
    At atm 
  | Neg (LStatA atm agt ldyn)
  | (LStatA atm agt ldyn) :&: (LStatA atm agt ldyn)
  | B agt (LStatA atm agt ldyn)
  | ldyn :□: (LStatA atm agt ldyn)

data ModelA' w agt atm = Model w (Map (w , agt) (Set w)) (Map w (LStatA atm agt (LDynA (ModelA' w agt atm))))

type Atm = String
type Agt = String
type World = String

type Model' = ModelA' World Agt Atm

instance Show Model' where
    show (Model w r pre) = w ++ ",\n" ++ show r ++ ",\n" ++ show pre

type L = LStatA Atm Agt (LDynA Model')


instance Show L where
    show (At a) = a
    show (Neg l) = "¬(" ++ show l ++ ")"
    show (l1 :&: l2) = show l1 ++ " ∧ " ++ show l2
    show (B agt l1) = "B " ++ agt ++ " " ++ show l1
    show (_ :□: l) = "[]" ++ show l

data TTermA label model formula agent = 
    Form label [model] formula 
  | Valid label [model]
  | Invalid label [model]
  | R label agent label
  | Bot

type Lab = Int
type TTerm = TTermA Lab Model' L Agt

deriving instance Eq Model'
deriving instance Eq L
deriving instance Eq TTerm

deriving instance Ord Model'
deriving instance Ord L
deriving instance Ord TTerm


addR :: (Ord w, Ord agt) => w -> agt -> w -> Map (w , agt) (Set w) -> Map (w , agt) (Set w)
addR w a u m = M.insertWith S.union (w , a) (S.singleton u) m

addRa :: (Ord w, Ord agt) => agt -> [(w, w)] -> Map (w , agt) (Set w) -> Map (w , agt) (Set w)
addRa a [] m = m
addRa a ((w , u) : xs) m = addR w a u $ addRa a xs m
