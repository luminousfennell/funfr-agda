module FunFr-20140627-template where

open import Prelude

module Types where
  -- (object-level) Types
  data Ty : Set where 
    N : Ty
    Fun : Ty → Ty → Ty

-- untyped lambda calculus
module LC where
  open Types

  -- Similar to Haskell's GADT syntax
  --   Set is like the kind *
  data Exp : Set where
    C : Nat → Exp
    Add : Exp → Exp → Exp
    Lam : Ty → Exp → Exp
    App : Exp → Exp → Exp
    Var : Nat → Exp

  idN : Exp 
  idN = Lam N (Var zero)
  
  constN : Exp 
  constN = Lam N (Lam N (Var 1))
  
  fortytwo = App (App constN (C 42)) (C 5)
  
  loop = App (Lam N (App (Var 0) (Var 0))) (Lam N (App (Var 0) (Var 0)))
  




module STLC where
  open Types

  -- Exp:
  -- We want a datatype where
  --   1) are all additions are on numbers  
  --   2) are all functions calls are on functions with correctly typed arguments
  --   3) are all used variables in scope
  
  -- let's tackle 1) and 2) first
  module Try1  where
    -- ... label (`index') the type of expressions with additional information
    -- ... namely the (object-level) type
    data Exp : Ty -> Set where
      C : Nat -> Exp N
      -- Add : 
      -- Lam : 
      -- App :
      -- -- Var: ?

    five : Exp N
    five = C 5
    
    fortytwo : Exp N
    fortytwo = {!!} -- 31 + 11

    const42 : Exp (Fun N N)
    const42 = {!!}  -- \ x -> 42

    constconst5 : Exp (Fun N (Fun N N))
    constconst5 = {!!} -- \ x y -> 5

    -- typeerror = ? -- (\ x -> x) + 5
    



    module SizeInterlude where

      -- interlude: interactive editing/how to write functions
      --    C-c C-l : (re)load file
      --    C-c C-c : case split (on variable written in goal)
      --    C-c .   : show type of current goal and context
      --    C-c ,   : show current goal
      --              and the type what's written inside it
      --    C-r     : refine/solve
      size : {t : Ty} -> Exp t -> Nat
      size e = {!!}

      
 
    -- tag-free evaluation

    -- eval' : {t : Ty} -> Exp t -> {! Value !} 
    -- eval' (C x) = {! x !}
    -- eval' (Add e1 e2) = {! eval' e1 + eval' e2 !}
    -- eval' (Lam t1 e) = {! λ x → eval' e!}
    -- eval' (App f e) = {! (eval' f) e!}

    test1 = {! eval (App const42 (C 5))!} 
    test2 = {! eval fortytwo!} 

  module Try2 where
  
    Ctx = List Ty
    {-
    data Exp : Ctx -> Ty -> Set where
      C : {G : Ctx} -> Nat -> Exp G N
      Add : {G : Ctx} -> Exp G N -> Exp G N -> Exp G N
      Lam : {G : Ctx} -> (t1 : Ty) {t2 : Ty} -> Exp (t1 :: G) t2 -> Exp G (Fun t1 t2)
      App : {G : Ctx} {t1 t2 : Ty} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
      Var : {G : Ctx} -> Nat -> Exp G {! lookup G n !}
    -}
    
    -- problem: lookup : Ctx -> n -> Ty = List Ty -> n -> Ty = (!!) which is partial

    -- solution: only allow pointers which are `bound'
    data Bound : Nat -> Ctx -> Set where
      -- zero : 
      -- suc : 
      
    -- now we can have a total lookup function
    lookupTy : {n : Nat} (G : Ctx) -> Bound n G -> Ty
    lookupTy x = {!!}


    data Exp : Ctx -> Ty -> Set where
      C : {G : Ctx} -> Nat -> Exp G N
      Add : {G : Ctx} -> Exp G N -> Exp G N -> Exp G N
      Lam : {G : Ctx} -> (t1 : Ty) {t2 : Ty} -> Exp (t1 :: G) t2 -> Exp G (Fun t1 t2)
      App : {G : Ctx} {t1 t2 : Ty} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
      Var : {G : Ctx} {n : Nat} (x : Bound n G) -> Exp G (lookupTy G x)
      
    -- idN : Exp nil (Fun N N)
    -- idN = Lam N (Var zero)
    
    -- constN : Exp nil (Fun N (Fun N N))
    -- constN = Lam N (Lam N (Var (suc zero)))
    
    -- fortytwo = App (App constN (C 42)) (C 5)

    -------------------
    -- evaluation:

    -- as before
    Value : Ty -> Set
    Value N = Nat
    Value (Fun t1 t2) = Value t1 → Value t2

    -- like in the tagger version, we need an environment:
    data Env : Ctx -> Set where
    
    
    eval : {G : Ctx} {t : Ty} -> Exp G t -> Env G -> Value t 
    eval (C x) _ = x
    eval (Add e1 e2) r = eval e1 r + eval e2 r
    eval (Lam t1 e) r = λ x → eval e ({! x :: r!})
    eval (App f e) r = eval f r (eval e r)
    eval (Var x) r = {! lookupV x r !}

    




  module Try3 where
    Ctx = List Ty

    data Bound : Ty -> Ctx -> Set where
      zero : {G : Ctx} {t : Ty} -> Bound t (t :: G)
      suc  : {t t' : Ty} {G : Ctx} -> Bound t G -> Bound t (t' :: G)



    data Exp : Ctx -> Ty -> Set where
      C : {G : Ctx} -> Nat -> Exp G N
      Add : {G : Ctx} -> Exp G N -> Exp G N -> Exp G N
      Lam : {G : Ctx} -> (t1 : Ty) {t2 : Ty} -> Exp (t1 :: G) t2 -> Exp G (Fun t1 t2)
      App : {G : Ctx} {t1 t2 : Ty} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2

      Var : {G : Ctx} {t : Ty} (x : Bound t G) -> Exp G t -- t == lookupTy x
      


    -- we can still define lookupTy, but it's no use
    --  as it *forgets* that it always returns t
    lookupTy : {t : Ty} (G : Ctx) -> Bound t G -> Ty 
    lookupTy nil ()
    lookupTy (t :: G) zero = t
    lookupTy (_ :: G) (suc x) = lookupTy G x
    



    
    Value : Ty -> Set
    Value N = Nat
    Value (Fun t1 t2) = Value t1 → Value t2

    data Env : Ctx -> Set where
      nil  : Env nil
      _::_ : {t : Ty} {G : Ctx} -> Value t -> Env G -> Env (t :: G)

    eval : {G : Ctx} {t : Ty} -> Exp G t -> Env G -> Value t 
    eval (C x) _ = x
    eval (Add e1 e2) r = eval e1 r + eval e2 r
    eval (Lam t1 e) r = λ x → eval e (x :: r)
    eval (App f e) r = eval f r (eval e r)
    eval (Var x) r = {! lookupV x r !}
    
    idN : Exp nil (Fun N N)
    idN = Lam N (Var zero)
    
    constN : Exp nil (Fun N (Fun N N))
    constN = Lam N (Lam N (Var (suc zero)))
    
    fortytwo = App (App constN (C 42)) (C 5)
    
    test = {! eval fortytwo nil!}

  open Try3 public

module Typeof where
  open Types
  open STLC hiding (lookupTy)
  open LC


  _==_ : (t1 t2 : Ty) → Maybe (t1 ≡ t2)
  t1 == t2 = {!!}
  

  data TypedIx (G : Ctx) : Set where
    ix : {t : Ty} -> Bound t G -> TypedIx G
  
  lookupTy : Nat -> (G : Ctx) -> Maybe (TypedIx G)
  lookupTy n G = {!!}
  
    
  data TypedResult (G : Ctx) : Set where
    result : {t : Ty} -> STLC.Exp G t -> TypedResult G
  
  typeof : (G : Ctx) → LC.Exp → Maybe (TypedResult G)
  typeof G e  = {!!}
       
  test-typeof-fortytwo :  typeof nil LC.fortytwo === just (result (App
                                                                 (App (Lam N (Lam N (Var (suc zero))))
                                                                  (C 42))
                                                                 (C 5)))
  test-typeof-fortytwo = refl
  
  data TypedValue : Set where
    val : {t : Ty} -> Value t -> TypedValue
  
  eval' : TypedResult nil -> TypedValue 
  eval' (result e) = val (eval e nil)

  test-eval-fortytwo : fmap eval' (typeof nil LC.fortytwo)  === just (val 42)
  test-eval-fortytwo = refl
