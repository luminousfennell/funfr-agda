-- TODO: link http://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/
module FunFr-20140627 where


open import Prelude

module Types where
  -- (object-level) Types
  -- Similar to Haskell's GADT syntax
  --   Set is like Kind *
  data Ty : Set where 
    N : Ty
    Fun : Ty → Ty → Ty

module LC where
  open Types

  data Exp : Set where
    C : Nat → Exp
    Add : Exp → Exp → Exp
    Lam : Ty → Exp → Exp
    App : Exp → Exp → Exp
    Var : Nat → Exp

  idN : Exp 
  idN = Lam N (Var zero)
  
  constN : Exp 
  constN = Lam N (Lam N (Var (suc zero)))
  
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
  
  -- ! This is a lambda calculus without variables! (not very usefull)
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
    

  -- ! show abbreviations
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
    
    
  -- show implicit arguments
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

    --    C-c ,   : show current goal
    --              and the type what's written inside it
    --    C-r     : refine/solve
    size : {t : Ty} -> Exp t -> Nat
    size (C x) = 1
    size (Add e1 e2) = suc (size e1 + size e2) -- we have e1, e2 in the context
    size (Lam t1 e) = suc (size e)
    size (App f e) = suc (size f + size e)
    

    -- tag free evaluation: 
    -- we have some programs... how about evaluating them

    eval' : {t : Ty} -> Exp t -> {! Value!} 
    -- We want to write this: no tags attached but what is the result
    -- type of the function?
    -- 
    -- when we look at the goal 0 we see that we have something to rely on: t
    -- sow we define Value as a function of t

    eval' (C x) = {! x !}
    eval' (Add e1 e2) = {! eval' e1 + eval' e2 !}
    eval' (Lam t1 e) = {! λ x → eval' e!}
    eval' (App f e) = {! (eval' f) e!}

    Value : Ty -> Set
    Value N = Nat
    Value (Fun t1 t2) = Value t1 → Value t2

    -- ! notice that the meta-variables differ in the goals !

    eval : {t : Ty} -> Exp t -> Value t 
    eval (C x) = x
    eval (Add e1 e2) = eval e1 + eval e2
    eval (Lam t1 e) = λ x → eval e
    eval (App f e) = eval f (eval e)
    
    test1 = {! eval (App ex3 ex-add)!} 
    test2 = {! eval ex-add!} 

    
  -- ok, but how do we deal with Var?
  module Try2 where
  
    -- In Exp we are doing something similar than in typeof (cf Haskell)
    -- ... so it's a good guess we need a *context*
  
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
      
    -- lookup function: pattern matching specialties
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
    
    -- like in the tagged version, we need an environment:
    data Env : Ctx -> Set where
      nil  : Env nil
      _::_ : {t : Ty} {G : Ctx} -> Value t -> Env G -> Env (t :: G)
    -- but now we can store untagged values, as we now the types from the Ctx
      

    eval : {G : Ctx} {t : Ty} -> Exp G t -> Env G -> Value t 
    eval (C x) _ = x
    eval (Add e1 e2) r = eval e1 r + eval e2 r
    eval (Lam t1 e) r = λ x → eval e (x :: r)
    eval (App f e) r = eval f r (eval e r)
    eval (Var x) r = lookupV x r
    -- does somebody now what could go wrong?
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

  open Try3 public


    
module Infer where
  open Types
  open STLC hiding (lookupTy)
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
  

  data TypedIx (G : Ctx) : Set where
    ix : {t : Ty} -> Bound t G -> TypedIx G
  
  lookupTy : Nat -> (G : Ctx) -> Maybe (TypedIx G)
  lookupTy n nil = nothing
  lookupTy zero (t :: G) = just (ix zero)
  lookupTy (suc n) (_ :: G) with lookupTy n G
  ... | just (ix x) = just (ix (suc x))
  ... | nothing = nothing
  
    
  data TypedResult (G : Ctx) : Set where
    result : {t : Ty} -> STLC.Exp G t -> TypedResult G
  
  typeof : (G : Ctx) → LC.Exp → Maybe (TypedResult G)
  typeof G (Var x) with lookupTy x G
  ... | just (ix x') = just (result (Var x'))
  ... | nothing = nothing
  typeof G (C x) = just (result (C x))
  typeof G (Add e1 e2) with typeof G e1 | typeof G e2
  ... | just (result {N} e1') | just (result {N} e2') = just (result (Add e1' e2'))
  ... | _ | _ = nothing
  typeof G (Lam t1 e) with typeof (t1 :: G) e
  typeof G (Lam t1 e) | just (result {t2} e') = just (result (Lam t1 e'))
  typeof G (Lam t1 e) | _ = nothing
  typeof G (App e1 e2) with typeof G e1 | typeof G e2
  typeof G (App e1 e2) | just (result {Fun t1 t2} f)   | just (result {t1'} e) with t1 == t1'
  typeof G (App e1 e2) | just (result {Fun t1 t2} f)   | just (result {.t1} e) | just refl = just (result (App f e))
  typeof G (App e1 e2) | just (result {Fun t1 t2} f)   | just (result {t1'} e) | nothing = nothing
  typeof G (App e1 e2) | _ | _ = nothing
       
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

module Typeof-Precise where
  open Types
  open STLC hiding (lookupTy)
  open LC
  open Infer using (_==_)

  --! we want to know that the indices are the basically the same
  bound-to-nat : {G : Ctx} {t : Ty} -> Bound t G -> Nat
  bound-to-nat zero = 0
  bound-to-nat (suc x) = suc (bound-to-nat x)
  
  -- ! and that the expressions are basically the same
  strip : {t : Ty} {G : Ctx} (e : STLC.Exp G t) -> LC.Exp
  strip (C x) = C x
  strip (Add e1 e2) = Add (strip e1) (strip e2)
  strip (Lam t1 e) = Lam t1 (strip e)
  strip (App f e) = App (strip f) (strip e)
  strip (Var x) = Var (bound-to-nat x)

  
  -- ! It is easier to state that as relations
  data BoundedIx : Nat -> Ty -> Ctx -> Set where
      zero : {G : Ctx} {t : Ty} -> BoundedIx zero t ( t :: G)
      suc  : {n : Nat} {t t' : Ty} {G : Ctx} -> BoundedIx n t G -> BoundedIx (suc n) t (t' :: G)

  toBound : {n : Nat} {t : Ty} {G : Ctx} -> BoundedIx n t G -> Bound t G
  toBound zero = zero
  toBound (suc x) = suc (toBound x)
      
  data Annotated {G : Ctx} : {t : Ty} -> LC.Exp -> STLC.Try3.Exp G t -> Set where
    Var : {t : Ty} {n : Nat} (x : BoundedIx n t G) -> Annotated (Var n) (Var (toBound x))
    C : {n : Nat} -> Annotated (C n) (C n)
    Add : {e1 e2 : LC.Exp} {e1' e2' : STLC.Exp G N} ->
          Annotated e1 e1' -> Annotated e2 e2' -> Annotated (Add e1 e2) (Add e1' e2')
    Lam : (t1 : Ty) {t2 : Ty} {e : LC.Exp} {e' : STLC.Exp (t1 :: G) t2} ->
          Annotated e e' -> Annotated (Lam t1 e) (Lam t1 e')
    App : {t1 t2 : Ty} {f e : LC.Exp} {f' : STLC.Exp G (Fun t1 t2)} {e' : STLC.Exp G t1} ->
          Annotated f f' -> Annotated e e' -> Annotated (App f e) (App f' e')

  
  -- the relation is correct wrt to the functions 
  lem-bound : {n : Nat} {t : Ty} {G : Ctx} -> (x : BoundedIx n t G) -> n === bound-to-nat (toBound x)
  lem-bound zero = refl
  lem-bound (suc x) = cong suc (lem-bound x)
          
  lem-annotated : {t : Ty} {G : Ctx} {e : LC.Exp} {e' : STLC.Exp G t} ->
                  Annotated e e' -> e === strip e'
  lem-annotated (Var x) = cong Var (lem-bound x)
  lem-annotated C = refl
  lem-annotated (Add e e') rewrite lem-annotated e | lem-annotated e' = refl
  lem-annotated (Lam t1 e) rewrite lem-annotated e = refl
  lem-annotated (App e e') rewrite lem-annotated e | lem-annotated e' = refl
  
  data TypedIx (G : Ctx) (n : Nat) : Set where
    ix : {t : Ty}  -> BoundedIx n t G -> TypedIx G n
  
  lookupTy-precise : (n : Nat) -> (G : Ctx) -> Maybe (TypedIx G n)
  lookupTy-precise n nil = nothing
  lookupTy-precise zero (t :: G) = just (ix zero)
  lookupTy-precise (suc n) (_ :: G) with lookupTy-precise n G
  ... | just (ix x) = just (ix (suc x))
  ... | nothing = nothing

  data TypedResult (G : Ctx) (e : LC.Exp) : Set where
    result : {t : Ty} {e' : STLC.Exp G t} -> Annotated e e' -> TypedResult G e

  typeof-precise : (G : Ctx) → (e : LC.Exp) → Maybe (TypedResult G e)
  typeof-precise G (Var x) with lookupTy-precise x G
  ... | just (ix  x') = just (result (Var x'))
  ... | nothing = nothing
  typeof-precise G (C x) = just (result C)
  typeof-precise G (Add e1 e2) with typeof-precise G e1 | typeof-precise G e2
  ... | just (result {t = N} e1') | just  (result {t = N} e2') = just (result (Add e1' e2'))
  ... | _ | _ = nothing
  typeof-precise G (Lam t1 e) with typeof-precise (t1 :: G) e
  typeof-precise G (Lam t1 e) | just (result {t = t2} e') = just (result (Lam t1 e'))
  typeof-precise G (Lam t1 e) | _ = nothing
  typeof-precise G (App e1 e2) with typeof-precise G e1 | typeof-precise G e2
  typeof-precise G (App e1 e2) | just (result {t = Fun t1 t2} f)   | just (result {t = t1'} e) with t1 == t1'
  typeof-precise G (App e1 e2) | just (result {t = Fun t1 t2} f) | just (result {t = .t1}  e) | just refl = just (result (App f e))
  typeof-precise G (App e1 e2) | just (result {t = Fun t1 t2} f)   | just (result {t = t1'} e)| nothing = nothing
  typeof-precise G (App e1 e2) | _ | _ = nothing
    
