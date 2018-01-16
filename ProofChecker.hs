module ProofChecker where

import AST
import qualified Data.Map.Strict as Map

type MatchingEnv = Map.Map Var (Maybe Formula)
data Error p = CannotProveError (Proof p) | GoalResMismatchError p | InvalidFrame p
 
takeAllProofs :: [Block p] ->  [Block p]
takeAllProofs [] = []
takeAllProofs (EAxiom _ _ : xs) = takeAllProofs xs
takeAllProofs ((p @ (EProof _ _ _ _)) : xs) = p : takeAllProofs xs


takeAllAxioms :: [Block p] -> [Formula]
takeAllAxioms [] = []
takeAllAxioms (EAxiom _ f : xs) =  f : takeAllAxioms xs
takeAllAxioms (EProof _ _ _ _ : xs) = takeAllAxioms xs


checkAllProofs :: Show p => [Formula] -> [Block p] -> String
checkAllProofs _ [] = ""
checkAllProofs axioms (pr : prs) = 
  getName pr ++ ": " ++ 
  case checkProof axioms pr of
    Right () ->  "OK\n" ++ checkAllProofs (getGoal pr : axioms) prs
    Left e -> 
      (case e of
        CannotProveError p -> "Cannot prove formula: " ++ show p ++ " starting at: " ++ (show $ getProofPos p)
        GoalResMismatchError p -> "You haven't proved the goal, in proof starting at: " ++ show p 
        InvalidFrame p -> "Invalid frame, at: " ++ show p)
      ++ "\n" ++ checkAllProofs axioms prs

      
checkProof :: [Formula] -> Block p -> Either (Error p) ()
checkProof _ (EAxiom _ _ ) = undefined
checkProof axioms (EProof p name goal proof) = 
  case extractRes proof of
    EFormula _ res ->
      if res == goal then
        tryToProve axioms [] proof    
      else
        Left $ GoalResMismatchError p
    otherwise -> Left $ GoalResMismatchError p    
  

extractRes :: Proof p ->  Proof p 
extractRes (ESeq s) = head $ reverse s
extractRes p = p


formulaFromProof :: Proof p -> Formula
formulaFromProof (EFormula _ f) = f
formulaFromProof _ =  NotAFormula


makeSingleVarMatchingEnv :: Formula -> Var -> MatchingEnv    
makeSingleVarMatchingEnv f x = Map.insert x Nothing (makeEnv f Map.empty)
  where 
    makeEnv :: Formula -> MatchingEnv -> MatchingEnv 
    makeEnv (EVar _) e = e
    makeEnv (EBool _) e = e   
    makeEnv (ENeg f) e = makeEnv f e
    makeEnv (EImp f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EIff f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EOr f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EAnd f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EAll x f) e = Map.insert x Nothing (makeEnv f e)   
    makeEnv (EExists x f) e = Map.insert x Nothing (makeEnv f e)   
    makeEnv NotAFormula e = e     


match :: MatchingEnv -> Formula -> Formula -> Bool
match e f1 f2 = _match f1 f2 e /= Nothing
  where
    _match :: Formula -> Formula -> MatchingEnv -> Maybe MatchingEnv
    _match (EBool x) (EBool y) e = return e
    _match (EVar x) f e = 
      if not (x `Map.member` e) then 
        if EVar x == f then
          return e
        else
          Nothing        
      else case e Map.! x of
        Nothing -> return $ Map.insert x (return f) e
        Just v -> if f /= v then Nothing else return e
    _match (ENeg f1) (ENeg f2) e = _match f1 f2 e
    _match (EImp f1 f2) (EImp f1' f2') e = _match f1 f1' e >>= \e2 -> _match f2 f2' e2      
    _match (EIff f1 f2) (EIff f1' f2') e = _match f1 f1' e >>= \e2 -> _match f2 f2' e2 
    _match (EOr  f1 f2) (EOr  f1' f2') e = _match f1 f1' e >>= \e2 -> _match f2 f2' e2 
    _match (EAnd f1 f2) (EAnd f1' f2') e = _match f1 f1' e >>= \e2 -> _match f2 f2' e2 
    
    _match (EAll x f1) (EAll y f2) e = do 
      e' <- _match f1 f2 $ Map.insert x (return $ EVar y) e 
      if x `Map.member` e then
        return $ Map.insert x (e Map.! x) e'
      else
        return $ Map.delete x e'
        
    _match (EExists x f1) (EExists y f2) e = do
      e' <- _match f1 f2 $ Map.insert x (return $ EVar y) e
      if x `Map.member` e then
        return $ Map.insert x (e Map.! x) e'
      else
        return $ Map.delete x e'
        
    
    _match _ _ _ = Nothing
  
  
checkIfProved :: [Proof p] -> Formula ->  Maybe ()
checkIfProved proved f = 
  if any ((f ==) .formulaFromProof) proved then Nothing
  else return ()
  
checkIfAxiom :: [Formula] -> Formula -> Maybe ()
checkIfAxiom axioms f = 
  if any (\f' -> match (makeEnv f' Map.empty) f' f) axioms then Nothing
  else return ()
  where
    makeEnv :: Formula -> MatchingEnv -> MatchingEnv 
    makeEnv (EVar x) e = Map.insert x Nothing e 
    makeEnv (EBool _) e = e   
    makeEnv (ENeg f) e = makeEnv f e
    makeEnv (EImp f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EIff f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EOr f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EAnd f1 f2) e = makeEnv f2 (makeEnv f1 e)
    makeEnv (EAll x f) e = Map.insert x Nothing (makeEnv f e)   
    makeEnv (EExists x f) e = Map.insert x Nothing (makeEnv f e)   
    makeEnv NotAFormula e = e 

        
introduce :: [Proof p] -> Formula ->  Maybe ()
introduce _ (EBool True) = Nothing

introduce ((EFrame _ ass pr) : proved) (ENeg f) = 
  case (extractRes pr) of
    EFormula _ (EBool False) -> if ass == f then Nothing
                                else return ()
    otherwise -> return ()

introduce ((EFrame _ ass pr) : proved) (EImp f1 f2) = 
  case extractRes pr of
    EFormula _ res -> if ass == f1 &&  res == f2 then Nothing
                      else return ()
    otherwise -> return ()
    
introduce ((EFrame _ ass1 pr1) : (EFrame _ ass2 pr2) : proved) (EIff f1 f2) = 
  case (extractRes pr1, extractRes pr2) of
    (EFormula _ res1, EFormula _ res2) -> 
      if (ass1 == f1 && res1 == f2 && ass2 == f2 && res2 == f1) || 
         (ass1 == f2 && res1 == f1 && ass2 == f1 && res2 == f2) then Nothing
      else return ()
    otherwise -> return ()

introduce proved (EOr f1 f2) = 
  if any ((==) f1 . formulaFromProof) proved || any ((==) f2 . formulaFromProof) proved then 
    Nothing
  else
    return ()

introduce proved (EAnd f1 f2) = 
  if any ((==) f1 . formulaFromProof) proved && any ((==) f2 . formulaFromProof) proved then 
    Nothing
  else
    return ()

introduce ((EAllFrame _ freshVar pr) : proved)  (EAll v f) = 
  if substitute (formulaFromProof $ extractRes pr) freshVar (EVar v) == f then 
    Nothing
  else
    return ()

introduce proved (EExists v f) = 
  if any (match (makeSingleVarMatchingEnv f v) f . formulaFromProof) proved then 
    Nothing 
  else 
    return ()
 
introduce _ _ = return ()


eliminateNeg :: [Proof p] -> Formula ->  Maybe ()
eliminateNeg proved (EBool False) =
  if any (\f -> any ((==) (ENeg $ formulaFromProof f) . formulaFromProof) proved) proved then Nothing
  else return ()
  
eliminateNeg _ _ = return ()

eliminateDoubleNeg :: [Proof p] -> Formula ->  Maybe ()
eliminateDoubleNeg proved f = 
  if any ((==) (ENeg (ENeg f)) . formulaFromProof) proved then Nothing
  else return ()  

eliminateAnd :: [Proof p] -> Formula ->  Maybe ()
eliminateAnd proved f = 
  if any (_match . formulaFromProof) proved then Nothing
  else return ()
  where 
    _match (EAnd f1 f2) = f == f1 || f == f2 || _match f1 || _match f2
    _match _ = False
   
eliminateImp :: [Proof p] -> Formula ->  Maybe ()  
eliminateImp proved f = 
  if any (_match . formulaFromProof) proved then Nothing
  else return ()
  where 
    _match (EImp f1 f2) = f2 == f && any ((f1 ==) . formulaFromProof) proved
    _match _ = False
    
eliminateIff :: [Proof p] -> Formula ->  Maybe ()  
eliminateIff proved f = 
  if any (_match . formulaFromProof) proved then Nothing
  else return ()
  where 
    _match (EIff f1 f2) = (f2 == f && any ((f1 ==) . formulaFromProof) proved) ||
                         (f1 == f && any ((f2 ==) . formulaFromProof) proved)
    _match _ = False
    
eliminateOr :: [Proof p] -> Formula ->  Maybe ()
eliminateOr ((EFrame _ ass1 pr1) : (EFrame _ ass2 pr2) : proved) f = 
  case (extractRes pr1, extractRes pr2) of
    (EFormula _ res1, EFormula _ res2) -> 
      if res1 == f && res2 == f && 
        any (_match . formulaFromProof) proved then Nothing
      else return ()  
    otherwise -> return ()
  where
    _match (EOr f1 f2) = (f1 == ass1 && f2 == ass2) || (f2 == ass1 && f1 == ass2)
    _match _ = False
    
eliminateOr _ _ = return ()

eliminateFalse :: [Proof p] -> Formula ->  Maybe ()
eliminateFalse proved _ = 
  if any ((EBool False ==) . formulaFromProof) proved then Nothing
  else return ()
  
eliminateAll :: [Proof p] -> Formula ->  Maybe ()  
eliminateAll proved f = 
  if any (_match . formulaFromProof) proved then Nothing 
  else return ()
  where 
    _match (EAll x f') = match (makeSingleVarMatchingEnv f' x) f' f
    _match _ = False  
    
eliminateExists :: [Proof p] -> Formula ->  Maybe ()    
eliminateExists (EExistsFrame _ v ass pr : proved) f = 
  if f == formulaFromProof (extractRes pr) && any ((EExists v ass ==) . formulaFromProof) proved then Nothing
  else return ()
  
eliminateExists _ _ = return ()
    
    
tryToProve :: [Formula] -> [Proof p] -> Proof p ->  Either (Error p) () 
tryToProve _ _ (ESeq []) = return ()
tryToProve axioms proved (ESeq (pr : prs)) = 
  tryToProve axioms proved pr >> tryToProve axioms (pr : proved) (ESeq prs)

tryToProve axioms proved (EFrame p ass pr) = 
  if formulaFromProof (extractRes pr) == NotAFormula then Left $ InvalidFrame p 
  else tryToProve axioms ((EFormula p ass) : proved) pr
  
tryToProve axioms proved (EAllFrame p v pr) = 
  if formulaFromProof (extractRes pr) == NotAFormula then Left $ InvalidFrame p 
  else tryToProve axioms proved pr
  
tryToProve axioms proved (EExistsFrame p v ass pr) = 
  if formulaFromProof (extractRes pr) == NotAFormula then Left $ InvalidFrame p 
  else tryToProve axioms ((EFormula p ass) : proved) pr

tryToProve axioms proved (x @ (EFormula p f)) = 
  case checkIfProved proved f >> 
       introduce proved f >> 
       checkIfAxiom axioms f >>
       eliminateOr proved f >> 
       eliminateExists proved f >>        
       eliminateNeg proved f >>
       eliminateDoubleNeg proved f >>
       eliminateAnd proved f >>
       eliminateImp proved f >> 
       eliminateIff proved f >> 
       eliminateFalse proved f >> 
       eliminateAll proved f 
  of
    Nothing -> return ()
    Just _ -> Left (CannotProveError x)
 
