module Prelude where

open import Data.Nat public
open import Data.Maybe public
open import Relation.Binary.PropositionalEquality public using (_≡_ ; refl ; cong) 

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A
infixr 5 _::_

data Sig (A : Set) (f : A -> Set) : Set where
  _,_ : (a : A) -> f a -> Sig A f
infixr 4 _,_

Nat = ℕ
_===_ = _≡_

fmap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
fmap f (just x) = just (f x)
fmap f nothing = nothing

