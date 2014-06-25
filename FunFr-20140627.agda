-- TODO: haskell version: what are tags? what can happen?
-- TODO: why is tag-free desirable?
module FunFr-20140627 where

open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality

module STLC where

  -- (object-level) Types
  data Ty : Set where -- ! explain Set
    N : Ty
    Fun : Ty → Ty → Ty
    
  Ctx = List Ty
  
  -- ! the definitions have to come one after each other
  infix 4 _∈_
  data _∈_ : Ty → Ctx → Set where
  -- !? how to explain implicit args?
    hd : {Γ : Ctx} {t : Ty} →  t ∈ t ∷ Γ
    tl : ∀ {Γ : Ctx} {t t' : Ty} → t ∈ Γ → t ∈ (t' ∷ Γ)
    
  -- Motivation: what can go wrong! What do we want to express!
  -- ! explain parameters and indexes
  data Exp (Γ : Ctx) : Ty → Set where
    C : ℕ → Exp Γ N 
    Add : Exp Γ N → Exp Γ N → Exp Γ N
    Lam : {t2 : Ty} (t1 : Ty) → Exp (t1 ∷ Γ) t2 → Exp Γ (Fun t1 t2) -- ! dependent function type syntax
    App : {t1 t2 : Ty} → Exp Γ (Fun t1 t2) → Exp Γ t1 → Exp Γ t2
    -- ! Explain the need of ∈
    Var : {t : Ty} → t ∈ Γ → Exp Γ t

  module ExampleTerms where
    n42 : Exp [] N
    n42 = C 42

    id : Exp [] (Fun N N) 
    id = Lam N (Var hd)
    
    const : Exp [] (Fun N (Fun N N))
    const = (Lam N (Lam N (Var (tl hd)))) 
    
    n5 n6 : Exp [] N
    n5 = App id (App (App const (C 5)) n42)
    n6 = Add n5 (C 1)
    
    -- ! Propositional Equality, refl, C-a, ?
    show-n5 : n5 ≡ App (Lam N (Var hd))
                        (App
                         (App (Lam N (Lam N (Var (tl hd))))
                               (C 5))
                         (C 42))
    show-n5 = refl
    

    -- ! interactive editing
    -- ! (infix stuff)
  ⟦_⟧ : Ty → Set
  ⟦ N ⟧ = ℕ
  ⟦ Fun t1 t2 ⟧ = ⟦ t1 ⟧ → ⟦ t2 ⟧
   
  data Env : Ctx → Set where
    [] : Env []
    _∷_ : {Γ : Ctx} {t : Ty} → ⟦ t ⟧ → Env Γ → Env (t ∷ Γ)
    
  -- ! the magic of dependent pattern matching
  lookup : {Γ : Ctx} {t : Ty} → t ∈ Γ → Env Γ → ⟦ t ⟧
  lookup hd (v ∷ ρ) = v
  lookup (tl x) (_ ∷ ρ) = lookup x ρ


  -- ! why is interpretation necessary? Usefull? (first step)
  -- ! why is Env necessary (second step), (third step is the lookup)
  eval : {Γ : Ctx} {t : Ty} → Exp Γ t → Env Γ → ⟦ t ⟧
  eval (C x) _ = x
  eval (Add e1 e2) ρ = eval e1 ρ + eval e2 ρ
  eval (Lam t1 e) ρ = λ x → eval  e (x ∷ ρ)
  eval (App f e) ρ = eval f ρ (eval e ρ)
  eval (Var x) ρ = lookup x ρ
  

  module ExampleEval where
     open ExampleTerms

     test-n6 : eval n6 [] ≡ 6
     test-n6 =  refl
     

module LC where
  open STLC using (Ty)

  data Exp : Set where
    Var : ℕ → Exp
    C : ℕ → Exp
    Add : Exp → Exp → Exp
    Lam : Ty → Exp → Exp
    App : Exp → Exp → Exp
    
module Infer where
  open STLC using (Ty ;Ctx; _∈_; hd; tl)

  -- Import the maybe Monad
  open import Data.Maybe
  open import Category.Monad
  import Level
  open RawMonad {Level.zero} Data.Maybe.monad
  
  -- ! explain equality
  -- ! explain with and rewriting
  _==_ : (t1 t2 : Ty) → Maybe (t1 ≡ t2)
  STLC.N == STLC.N = just refl
  STLC.N == STLC.Fun _ _ = nothing
  STLC.Fun t1 t2 == STLC.N = nothing
  STLC.Fun t1 t2 == STLC.Fun t3 t4 with t1 == t3 | t2 == t4 
  ... | just p1 | just p2 = just (cong₂ STLC.Fun p1 p2)
  ... | _       | _      = nothing
  
  lookupTy : ℕ → (t : Ty) (Γ : Ctx) → Maybe (t ∈ Γ)
  lookupTy _ _ [] = nothing
  lookupTy zero t (t' ∷ Γ) with t == t'
  -- ! explain dotted patterns
  lookupTy zero .t' (t' ∷ Γ) | just refl = just hd
  ... | nothing = nothing
  lookupTy (suc x) t (_ ∷ Γ) = tl <$> lookupTy x t Γ
  
  open import Data.Product
  
  -- ! explain exists
  lookupInferTy : ℕ → (Γ : Ctx) → Maybe (∃ (λ t → t ∈ Γ))
  lookupInferTy _ [] = nothing
  lookupInferTy zero (x ∷ Γ) = just (x , hd)
  lookupInferTy (suc n) (_ ∷ Γ) with lookupInferTy n Γ
  ... | just (t , x) = just (t , tl x)
  ... | nothing = nothing
  
  -- there is a typed STCL Expression; better (TODO) such that the erasure is equal to the untyped one
  infer : (Γ : Ctx) → LC.Exp → Maybe (∃ (λ t → STLC.Exp Γ t))
  infer Γ (LC.Var x) with lookupInferTy x Γ
  ... | just (t , x') = just (t , STLC.Var x')
  ... | nothing = nothing
  infer Γ (LC.C x) = just (STLC.N , STLC.C x)
  infer Γ (LC.Add e1 e2) with infer Γ e1 | infer Γ e2
  ... | just (STLC.N , e1') | just (STLC.N , e2') = just (STLC.N , STLC.Add e1' e2')
  ... | _ | _ = nothing
  infer Γ (LC.Lam t1 e) with infer (t1 ∷ Γ) e
  infer Γ (LC.Lam t1 e) | just (t2 , e') = just (STLC.Fun t1 t2 , STLC.Lam t1 e')
  infer Γ (LC.Lam t1 e) | _ = nothing
  infer Γ (LC.App e1 e2) with infer Γ e1 | infer Γ e2
  infer Γ (LC.App e1 e2) | just (STLC.Fun t1 t2 , f)   | just (t1' , e) with t1 == t1'
  infer Γ (LC.App e1 e2) | just (STLC.Fun .t1' t2 , f) | just (t1' , e) | just refl = just (t2 , STLC.App f e)
  infer Γ (LC.App e1 e2) | just (STLC.Fun t1 t2 , f)   | just (t1' , e) | nothing = nothing
  infer Γ (LC.App e1 e2) | _ | _ = nothing
       
