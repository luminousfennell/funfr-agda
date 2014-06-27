-- TODO: haskell version: what are tags? what can happen?
-- TODO: why is tag-free desirable?
-- TODO: basic dependent function type syntax (with implicit arguments)
-- TODO: link http://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/
module FunFr-20140627 where


open import Prelude

module Types where
  -- (object-level) Types
  data Ty : Set where 
    N : Ty
    Fun : Ty → Ty → Ty

module STLC where
  open Types

    
  -- Similar to Haskell's GADT syntax
  --   Set is like Kind *
  
  -- Exp:
  -- We want a datatype where
  --   1) are all additions are on numbers  
  --   2) are all functions calls are on functions with correctly typed arguments
  --   3) are all used variables in scope
  
  -- let's tackle 1) and 2) first
  module Try1  where
    data Exp : Ty -> Set where
      C : Nat -> Exp N
      Add : Exp N -> Exp N -> Exp N
      Lam : (t1 : Ty) -> (t2 : Ty) -> Exp t2 -> Exp (Fun t1 t2)
      App : (t1 : Ty) -> (t2 : Ty) -> Exp (Fun t1 t2) -> Exp t1 -> Exp t2
      -- Var: ?
      
    -- write them down later
    ex1 : Exp N
    ex1 = C 5
    ex2 : Exp (Fun N N)
    ex2 = Lam N N (C 42)
    ex3 : Exp (Fun N (Fun N N))
    ex3 = Lam N (Fun N N) (Lam N N (C 5))
    
    ex-add = Add (C 5) (C 6)
    -- ex-add-fail = Add (C 5) (Lam N N (C 5))
    
  module Try1' where
    -- make signatures more concise 
    data Exp : Ty -> Set where
      C : Nat -> Exp N
      Add : Exp N -> Exp N -> Exp N
      Lam : (t1 : Ty) (t2 : Ty) -> Exp t2 -> Exp (Fun t1 t2)
      App : (t1 t2 : Ty) -> Exp (Fun t1 t2) -> Exp t1 -> Exp t2
      --     ^ even more consise
      --       (there's an even shorter version; not shown)
      -- Var: ?
      
    ex1 : Exp N
    ex1 = C 5
    ex2 : Exp (Fun N N) 
    ex2 = Lam N N (C 42)
    ex3 : Exp (Fun N (Fun N N))
    ex3 = Lam N (Fun N N) (Lam N N (C 5))
    
    
  module Try1'' where
    -- make examples more concise with implicit arguments
    data Exp : Ty -> Set where
      C : Nat -> Exp N
      Add : Exp N -> Exp N -> Exp N
      Lam : (t1 : Ty) {t2 : Ty} -> Exp t2 -> Exp (Fun t1 t2)
      App : {t1 t2 : Ty}  -> Exp (Fun t1 t2) -> Exp t1 -> Exp t2
      -- Var: ?
      
    ex1 : Exp N
    ex1 = C 5
    ex2 : Exp (Fun N N) 
    -- why? the type signature already defines the return value
    ex2 = Lam N (C 42)
    -- but the implicit argument can always be given explicitly
    ex2' : Exp (Fun N N)
    ex2' = Lam N {N} (C 42)
    ex3 : Exp (Fun N (Fun N N))
    -- why? same reason
    ex3 = Lam N (Lam N (C 5))
    
    ex-add = Add (C 5) (C 6)
    -- ex-add-fail = Add (C 5) (Lam N N (C 5))
    
    -- interlude: interactive editing/how to write functions
    --    C-c C-l : (re)load file
    --    C-c C-c : case split (on variable written in goal)
    --    C-c .   : show current goal
    --    C-c ,   : show current goal
    --              and the type what's written inside it
    --    C-r     : refine/solve
    size : {t : Ty} -> Exp t -> Nat
    size (C x) = 1
    size (Add e1 e2) = suc (size e1 + size e2) -- we have e1, e2 in the context
    size (Lam t1 e) = suc (size e)
    size (App f e) = suc (size f + size e)
    

    -- tag free evaluation
    eval' : {t : Ty} -> Exp t -> {! Value!} 
    -- We want to write this: no tags attached but what is the result
    -- type of the function? when we look at the goal 0 we see that we
    -- have something to rely on: t
    eval' (C x) = {! x !}
    eval' (Add e1 e2) = {! eval' e1 + eval' e2 !}
    eval' (Lam t1 e) = {! λ x → eval' e!}
    eval' (App f e) = {! (eval' f) e!}

    Value : Ty -> Set
    Value N = Nat
    Value (Fun t1 t2) = Value t1 → Value t2

    -- notice that the meta-variables differ in the goals
    eval : {t : Ty} -> Exp t -> Value t 
    eval (C x) = x
    eval (Add e1 e2) = eval e1 + eval e2
    eval (Lam t1 e) = λ x → eval e
    eval (App f e) = eval f (eval e)
    
    test1 = {! eval (App ex3 ex-add)!} 
    test2 = {! eval ex-add!} 

    
  -- ok, but how do we deal with Var?
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

    -- ! constructors can be overloaded
    data Bound : Nat -> Ctx -> Set where
      zero : {G : Ctx} {t : Ty} -> Bound zero ( t :: G)
      suc  : {n : Nat} {t : Ty} {G : Ctx} -> Bound n G -> Bound (suc n) (t :: G)
      
    lookupTy : {n : Nat} (G : Ctx) -> Bound n G -> Ty
    lookupTy nil ()
    lookupTy (t :: G) zero = t
    lookupTy (_ :: G) (suc x) = lookupTy G x

    data Exp : Ctx -> Ty -> Set where
      C : {G : Ctx} -> Nat -> Exp G N
      Add : {G : Ctx} -> Exp G N -> Exp G N -> Exp G N
      Lam : {G : Ctx} -> (t1 : Ty) {t2 : Ty} -> Exp (t1 :: G) t2 -> Exp G (Fun t1 t2)
      App : {G : Ctx} {t1 t2 : Ty} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
      Var : {G : Ctx} {n : Nat} (x : Bound n G) -> Exp G (lookupTy G x)
      
    idN : Exp nil (Fun N N)
    idN = Lam N (Var zero)
    
    constN : Exp nil (Fun N (Fun N N))
    constN = Lam N (Lam N (Var (suc zero)))
    
    fortytwo = App (App constN (C 42)) (C 5)

    Value : Ty -> Set
    Value N = Nat
    Value (Fun t1 t2) = Value t1 → Value t2
    
    -- how to evaluate those?
    -- eval : {G : Ctx} {t : Ty} -> Exp G t -> {!!} -> Value t 
    -- eval e r = {!!}
    data Env : Ctx -> Set where
      nil  : Env nil
      _::_ : {t : Ty} {G : Ctx} -> Value t -> Env G -> Env (t :: G)
      

    eval : {G : Ctx} {t : Ty} -> Exp G t -> Env G -> Value t 
    eval (C x) _ = x
    eval (Add e1 e2) r = eval e1 r + eval e2 r
    eval (Lam t1 e) r = λ x → eval e (x :: r)
    eval (App f e) r = eval f r (eval e r)
    eval (Var x) r = lookupV x r
      where lookupV : {G : Ctx} {n : Nat} ->
                      Bound n G -> Env G -> Value (lookupTy _ x)
            lookupV () nil
            lookupV zero (v :: r') = {! v!}
            --  ^^ does not work: lookupTy .G x /= .t (in general)
            lookupV (suc x) (_ :: r') = lookupV x r'
            
  -- Problem: we do not know if x points to the right type.
  -- ... why does it? Because we say so in Lam (show that!)
  -- ... how can we let Agda now?
  -- Solution: attach the variable-type to the (type of) the index
    
  module Try3 where
    Ctx = List Ty

    -- ! constructors can be overloaded
    data Bound : Ty -> Ctx -> Set where
      zero : {G : Ctx} {t : Ty} -> Bound t ( t :: G)
      suc  : {t t' : Ty} {G : Ctx} -> Bound t G -> Bound t (t' :: G)


    data Exp : Ctx -> Ty -> Set where
      C : {G : Ctx} -> Nat -> Exp G N
      Add : {G : Ctx} -> Exp G N -> Exp G N -> Exp G N
      Lam : {G : Ctx} -> (t1 : Ty) {t2 : Ty} -> Exp (t1 :: G) t2 -> Exp G (Fun t1 t2)
      App : {G : Ctx} {t1 t2 : Ty} -> Exp G (Fun t1 t2) -> Exp G t1 -> Exp G t2
      Var : {G : Ctx} {t : Ty} (x : Bound t G) -> Exp G t -- t == lookupTy x

    -- lookupTy is now trivial: (we do not even have to look at Bound)... but it's type forgets that
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
    eval (Var x) r = lookupV x r
      where lookupV : {G : Ctx} {t : Ty} ->
                      Bound t G -> Env G -> Value t
            lookupV () nil
            lookupV zero (v :: r') = v
            lookupV (suc x) (_ :: r') = lookupV x r'
  
    idN : Exp nil (Fun N N)
    idN = Lam N (Var zero)
    
    constN : Exp nil (Fun N (Fun N N))
    constN = Lam N (Lam N (Var (suc zero)))
    
    fortytwo = App (App constN (C 42)) (C 5)
    
    test = {! eval fortytwo nil!}


module LC where
  open Types

  data Exp : Set where
    Var : Nat → Exp
    C : Nat → Exp
    Add : Exp → Exp → Exp
    Lam : Ty → Exp → Exp
    App : Exp → Exp → Exp

  idN : Exp 
  idN = Lam N (Var zero)
  
  constN : Exp 
  constN = Lam N (Lam N (Var (suc zero)))
  
  fortytwo = App (App constN (C 42)) (C 5)
  
  loop = App (Lam N (App (Var 0) (Var 0))) (Lam N (App (Var 0) (Var 0)))
    
module Infer where
  open Types
  open STLC.Try3 hiding (lookupTy)
  open LC


  -- ! explain equality
  -- ! explain with and rewriting
  _==_ : (t1 t2 : Ty) → Maybe (t1 ≡ t2)
  N == N = just refl
  N == Fun _ _ = nothing
  Fun t1 t2 == N = nothing
  Fun t1 t2 == Fun t3 t4 with t1 == t3 | t2 == t4 
  ... | just p1 | just p2 rewrite p1 | p2 = just refl
  ... | _       | _       = nothing
  
  lookupTy : Nat -> (G : Ctx) -> Maybe (Sig Ty (\ t -> Bound t G)) 
  lookupTy n nil = nothing
  lookupTy zero (t :: G) = just (t , zero)
  lookupTy (suc n) (_ :: G) with lookupTy n G
  ... | just (t , x) = just (t , suc x)
  ... | nothing = nothing
  
  -- there is a typed STCL Expression; better (TODO) such that the erasure is equal to the untyped one
  typeof : (G : Ctx) → LC.Exp → Maybe (Sig Ty (\ t -> STLC.Try3.Exp G t))
  typeof G (Var x) with lookupTy x G
  ... | just (t , x') = just (t , Var x')
  ... | nothing = nothing
  typeof G (C x) = just (N , C x)
  typeof G (Add e1 e2) with typeof G e1 | typeof G e2
  ... | just (N , e1') | just (N , e2') = just (N , Add e1' e2')
  ... | _ | _ = nothing
  typeof G (Lam t1 e) with typeof (t1 :: G) e
  typeof G (Lam t1 e) | just (t2 , e') = just (Fun t1 t2 , Lam t1 e')
  typeof G (Lam t1 e) | _ = nothing
  typeof G (App e1 e2) with typeof G e1 | typeof G e2
  typeof G (App e1 e2) | just (Fun t1 t2 , f)   | just (t1' , e) with t1 == t1'
  typeof G (App e1 e2) | just (Fun .t1' t2 , f) | just (t1' , e) | just refl = just (t2 , App f e)
  typeof G (App e1 e2) | just (Fun t1 t2 , f)   | just (t1' , e) | nothing = nothing
  typeof G (App e1 e2) | _ | _ = nothing
       
  test-typeof-fortytwo :  typeof nil LC.fortytwo === just (N , App
                                                                 (App (Lam N (Lam N (Var (suc zero))))
                                                                  (C 42))
                                                                 (C 5))
  test-typeof-fortytwo = refl
  
  eval' : (Sig Ty (\ t -> STLC.Try3.Exp nil t)) -> Sig Ty (\ t -> Value t)
  eval' ( t , e ) = t , eval e nil

  test-eval-fortytwo : fmap eval' (typeof nil LC.fortytwo)  === just (N , 42)
  test-eval-fortytwo = refl
