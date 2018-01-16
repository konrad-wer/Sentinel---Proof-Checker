module AST where

import Control.Applicative
import Control.Monad

type Var = String

-------------------------------LabelState---------------------------------

newtype LabelState b = LabelState (Int -> (b, Int)) 

run :: LabelState b -> Int -> (b, Int)
run (LabelState f) s = f s

freshLabel :: LabelState Var
freshLabel = LabelState (\s -> ("_" ++ show s, s + 1))

ls_and :: LabelState Bool -> LabelState Bool -> LabelState Bool 
ls_and f g = f >>= \r1 -> g >>= \r2 -> return (r1 && r2)

instance Monad LabelState where
  return x = LabelState (\s -> (x, s))
  f >>= g  = LabelState (\s -> let (v, s') = run f s in run (g v) s')

instance Functor LabelState where
  fmap = liftM
  
instance Applicative LabelState where
  pure x = LabelState(\s -> (x, s))
  (<*>) = ap

--------------------------------------------------------------------------

data Block p = 
    EProof p Var Formula (Proof p)
  | EAxiom p Formula 
  
getName :: Block p -> Var  
getName (EProof _ name _ _ ) = name
getName _ = ""  

getGoal :: Block p -> Formula
getGoal (EProof _ _ g _) = g
getGoal (EAxiom _ g) = g

data Proof p = 
    ESeq [Proof p]
  | EFrame p Formula (Proof p)
  | EAllFrame p Var (Proof p)
  | EExistsFrame p Var Formula (Proof p)
  | EFormula p Formula
  
getProofPos (EFrame p _ _) = p
getProofPos (EAllFrame p _ _) = p
getProofPos (EExistsFrame p _ _ _) = p
getProofPos (EFormula p _) = p
getProofPos _ = undefined



data Formula = 
    EVar Var
  | EBool Bool
  | ENeg Formula
  | EImp Formula Formula
  | EIff Formula Formula
  | EOr Formula Formula
  | EAnd Formula Formula 
  | EAll Var Formula 
  | EExists Var Formula 
  | NotAFormula 
  
substitute :: Formula -> Var -> Formula -> Formula
substitute (f @ (EVar x)) v t = 
  if v == x then t 
  else f
  
substitute (f @ (EBool _)) _ _ = f   
substitute (ENeg f) v t = ENeg $ substitute f v t
substitute (EImp f1 f2) v t = (EImp $ substitute f1 v t) $ substitute f2 v t 
substitute (EIff f1 f2) v t = (EIff $ substitute f1 v t) $ substitute f2 v t 
substitute (EAnd f1 f2) v t = (EAnd $ substitute f1 v t) $ substitute f2 v t
substitute (EOr f1 f2) v t  = (EOr  $ substitute f1 v t) $ substitute f2 v t

substitute (f @ (EAll x b)) v t = 
  if x == v then f
  else EAll x $ substitute b v t

substitute (f @ (EExists x b)) v t = 
  if x == v then f
  else EExists x $ substitute b v t
  
substitute NotAFormula _ _ = NotAFormula

instance Eq Formula where
  (==) a b = fst $ run (checkEq a b) 0
    where
      checkEq :: Formula -> Formula -> LabelState Bool
      checkEq NotAFormula NotAFormula = return True
      checkEq (EVar x) (EVar y) = return (x == y)
      checkEq (EBool b1) (EBool b2) = return (b1 == b2)
      checkEq (ENeg f1) (ENeg f2) = checkEq f1 f2
      checkEq (EImp f1 f2) (EImp f1' f2') = checkEq f1 f1' `ls_and` checkEq f2 f2' 
      checkEq (EIff f1 f2) (EIff f1' f2') = checkEq f1 f1' `ls_and` checkEq f2 f2' 
      checkEq (EAnd f1 f2) (EAnd f1' f2') = checkEq f1 f1' `ls_and` checkEq f2 f2' 
      checkEq (EOr f1 f2)  (EOr f1' f2')  = checkEq f1 f1' `ls_and` checkEq f2 f2' 
    
      checkEq  (EAll x1 f1) (EAll x2 f2) = do
        lbl <- freshLabel
        checkEq (substitute f1 x1 $ EVar lbl) (substitute f2 x2 $ EVar lbl) 

      checkEq  (EExists x1 f1) (EExists x2 f2) = do
        lbl <- freshLabel
        checkEq (substitute f1 x1 $ EVar lbl) (substitute f2 x2 $ EVar lbl) 

      checkEq _ _ = return False

   
instance Show Formula where
  show (EVar x) = x
  show (EBool True) = "True"
  show (EBool False) = "False"
  show (ENeg x) = "~" ++ show x
  show (EImp x y) = "(" ++ show x ++ " => " ++ show y ++ ")"
  show (EIff x y) = "(" ++ show x ++ " <=> " ++ show y ++ ")"
  show (EOr x y) = "(" ++ show x ++ " v " ++ show y ++ ")"
  show (EAnd x y) = "(" ++ show x ++ " ^ " ++ show y ++ ")"
  show (EAll v f) = "All " ++ show v ++ " : " ++ show f 
  show (EExists v f) = "Exists " ++ show v ++ " : " ++ show f 
  
  
instance Show (Proof p) where
  show (ESeq p1) = show p1  
  show (EFrame p a p1) = "[" ++ show a ++ " : " ++ show p1 ++ "]" 
  show (EAllFrame p v p1) = "[" ++ show v ++ " | " ++ show p1 ++ "]" 
  show (EExistsFrame p v a p1) = "[" ++ show v ++" | " ++  show a ++ " : " ++ show p1 ++ "]" 
  show (EFormula p f) =  "(" ++ show f ++ ")"
  
instance Show (Block p) where
  show (EProof p name g pr) =  "Proof: " ++  name ++ ", Goal: " ++ show g ++ ", proof: " ++ show pr
  show (EAxiom p f) = "Axiom: " ++ show f 
  
  