module Prelude where

open import Data.Nat public

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A
infixr 5 _::_

Nat = ℕ
