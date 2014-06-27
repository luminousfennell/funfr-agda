module STCL where

import Data.List
import Control.Monad

-- Syntax 
data Ty = N | Fun Ty Ty
  deriving (Show, Eq)
           
data Exp = C Int
         | Add Exp Exp
         | Lam Ty Exp  -- Functions explicitly type their arguments
         | App Exp Exp
         | Var Int
  deriving (Show)
           
fortytwo, constN, ex :: Exp
fortytwo = Add (C 31) (C 11)
constN = Lam N (Lam N (Var 1))
         
ex = App (App constN fortytwo) (C 5) 
          
          
-- evaluation
data Value = VNum Int | VClos (Value -> Value)          
--           ^ this is the `tag'
instance Show Value where
  show (VNum x) = "VNum " ++ show x
  show (VClos _) = "VClos"
type Env = [Value]

eval :: Exp -> Env -> Value
eval (C x)       _ = VNum x
eval (Add e1 e2) r | (VNum x1, VNum x2) <- (eval e1 r, eval e2 r)
                     =  VNum (x1 + x2)
                   | otherwise
                     = error "ill-typed addition"
eval (Lam t e)   r = VClos (\x -> eval e (x:r))
eval (App f e)   r | (VClos vf, v) <- (eval f r, eval e r) 
                     = vf v
                   | otherwise
                     = error "ill-typed function call"
eval (Var x)     r | x < length r = r !! x
                   | otherwise = error "variable not in scope"

                                 
-- Problems:

-- run-time errors
exfail = Add constN fortytwo 

-- loops
exloop = App (Lam N (App (Var 0) (Var 0))) (Lam N (App (Var 0) (Var 0)))
         
-- Of course we can type-check an expression:
type Ctx = [Ty]
         
typeof :: Exp -> Ctx -> Maybe Ty
typeof (C _) _ = return N
typeof (Add e1 e2) g = do
  N <- typeof e1 g
  N <- typeof e2 g
  return N
typeof (Lam t1 e) g = do
  t2 <- typeof e (t1 : g)
  return (Fun t1 t2)
typeof (Var x) g = do
  guard (x < length g)
  return (g !! x)
typeof (App f e) g = do
  Fun t1 t2 <- typeof f g
  t <- typeof e g
  guard (t1 == t)
  return t2
  
-- But we can forget to do it (or do it too often),
--   and eval still has to pattern-match on Value

