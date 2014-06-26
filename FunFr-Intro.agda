module FunFr-Intro where
-- We have hardly anything predefined. Agda has no implicit Prelude.
-- five = 3 + 2 -- Not in scope: +

------
-- Unary natural numbers as an algebraic datatype
------
-- similar to Haskell's GADT syntax, but
--   instead of kind * we have Set
--   type assignment operator is _:_
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
  
three : Nat
three = suc (suc (suc zero))
  
-- There is syntax sugar for natural numbers
{-# BUILTIN NATURAL Nat    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
fortytwo : Nat
fortytwo = 42

-------
-- Defining the function `minus' on natural numbers
------
-- -- start like this:

-- minus' : Nat → Nat → Nat
-- minus' n m = ?

-- -- and then use agda-mode magic to fill in the solution
--    C-c C-l : (re)load file
--    C-c C-c : case split (on variable written in goal)
--    C-c .   : show current goal
--    C-c ,   : show current goal
--              and the type what's written inside it
--    C-r     : refine/solve


minus' : Nat -> Nat -> Nat
minus' n zero = n
minus' zero (suc m) = zero -- ! that's not like the `minus' you learn in grammar school !
minus' (suc n) (suc m) = minus' n m

ex-minus'1 : Nat
ex-minus'1 = minus' three fortytwo -- = 0, check with C-c C-n

-- what if we only want to subtract like in grammar school?
-- We could
--   1. be careful and only call minus' n m where m >= n
--   2. use Haskell and make the function partial 
--      
        -- minus' :: Nat → Nat → Nat
        -- minus' n zero = n
        -- minus' zero (suc m) = error "leaving the natural numbers"
        -- minus' (suc n) (suc m) = minus' n m
---------
--   3. use Agda and *Dependent Types*
--------

--       
--       1) `minus should be called with two natural numbers, where the second is smaller than the first'
--       2) `the result is a natural number'
--       3) `and this function is *total*' i.e., it always terminates and never gives an error!'
--  How do we express this as a type?

-- Nat → Nat → Nat
--   means: `should be called with two natural numbers, result is natural number, and is total'

-- missing: `where the second is smaller than the first'

-- ! mixfix syntax:
--    can write anything but spaces (and some parens) and put _ where the arguments belong.

data _<=_ : Nat -> Nat -> Set where
  z<=n : (n : Nat) -> zero <= n -- dependent type signature
  s<=s : (n : Nat) -> (m : Nat) -> n <= m -> n <= suc m
  -- alternative syntax:
  -- s<=s : (n : Nat) (m : Nat) -> n <= m -> n <= suc m
  -- s<=s : (n m : Nat) -> n <= m -> n <= suc m
  
-- Explanation:
-- data _<=_ : Nat -> Nat -> Set where 
--   type constructor: construct a Set (i.e., type) given two *NatS*
--   or: the family of all types constructable by _<=_ is a relation on natural numbers

-- z<=n : (n : Nat) -> zero <= n 
--   value constructor: given the Nat n, I can give you an element of zero <= n
--  s<=s : (n : Nat) -> (m : Nat) -> n <= m -> n <= suc m
--   value constructor: given the NatS n m, and an element of n <= m, i can give you an element of n <= suc m

-- TODO: Beispiele für Elemente

minus'' : (n m : Nat) -> m <= n -> Nat
minus'' n .0 (z<=n .n) = n
minus'' .(suc n) m (s<=s .m n m<=n) = minus'' n m m<=n

minus : {n m : Nat} -> m <= n -> Nat
minus {n} (z<=n .n) = n
minus {.(suc m₁)} {m} (s<=s .m m₁ m<=n) = m₁
