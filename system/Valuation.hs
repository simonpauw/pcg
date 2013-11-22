module Valuation where

import Data.List
import Data.Maybe

{- 
Project: Disjunctive Frame Unifier
Simon Pauw, 2013
-}

{-
Explanation

1) Basic concepts
Formal definitions

The unfication mechanisms deals with two types of unifications:
Assignments: var x has value a (x,a)
Constraints: var x and var y refer to the same value (x,y)

The assignment is the result of assigning a specific value to a feature in the language system (i.e. case="nominative")
The constraint is the result of equating two features (i.e. np.referent==determiner.referent)

Formally:
-The constraint (Var,Var) defines an equivalence class over the variables.
so for all x,y,z it holds that: 1) (x,x), 2) (x,y) -> (y,x), and 3) (x,y) and (y,z) -> (x,z)
-The assignment (Var, Val) is unique for an equivalence class.
So for all values a and all variables x and y: 1) (x,a) and (x,y) -> (y,a) and 2) (x,a) and (y,b) -> a = b

For efficiency the variables are unique integer values.


2) DisjunctiveFrames
Often language can attribute multiple possible assignments to features.

For example the english pos 'have':  
(Example 1)
(tense="present", number="singular", person="first") or 
(tense="present", number="singular", person="second") or 
(tense="present", number="plural", person="first") or
(tense="present", number="plural", person="second") or
(tense="present", number="plural", person="third")

Which can be summarized as:
(Example 2)
[(tense="present")] and [(number="singular", person="first") or (number="singular", person="second") or (number="plural")]

- Essentially (number="singular", person="first") is a list of features that belong together, which is called a ConjunctiveFrame (CF)
- Then, the disjunction [(number="singular", person="first") or (number="singular", person="second") or (number="plural")] is 
simply a disjunctive list of competing CFs, called a DisjunctiveFrame (DF)
- The whole meaning of Example 2 can be represented as a conjunctive list of (DFs) called a ValutationAssignmentFrame (VAF)

All possible valuations can be gotten by computing the cartesian product of all DisjunctiveFrames
E.g.: 
[(tense="present")] (X) [(number="singular", person="first"),(number="singular", person="second"),...]=
[tense="present", number="singular", person="first"],[tense="present", number="singular", person="second"],...

Such an expansian grows exponentially with the amount of disjunctive frames. The key to the present algorithm is exactly to not to expand.

Essential to the algorithm is to keep assignments and constraints separted. By garenteeing that the DF can only contain assignments, 
we can efficiently compute (polynomially instead of exponentially) the effects of adding new information to the valuation.

3) Algorithm
Two operations can add information to a Valuation:
- addConstraints 
- addDF

The notion of compatibility is essential for understanding these operations
- Two assignments are NOT compatible if they relate variables of the same class to different values (x,a) and (y,a) and (x,y),
  otherwise they are compatible.
- Two CFs are compatible if all their assignments are mutually compatible.
- a CF (cf1) is compatible with a DF if the DF contains at least one CF (cf2) that is compatible with cf1.

- The operation removeIncompatibleCFs takes two DFs (df1 and df2) and removes all CFs in df1 that are not compatible with df2. It returns the modified df1.
  Everytime we modify a DF we need to check the inpact on the other DFs. 
- The operation pullDFs takes a token DF and a list of DFs and 
  1) finds all that are effected by removeIncompatibleCFs (dfs_affected), 2) applies the operation removeIncompatibleCFs to dfs_affected and 
  3) creates a queue of dfs_affected to which we can recursively apply pullDFs again by using processDFsQueue
  The last step is needed since the modification of any of the DFs in dfs_affected can have consquences for the remaining DFs

Now the two functions are quite simple:
- addConstraints 
    1) adds a number of variable constraints (x, y) to the Valuation. 
      For very constraint (x,y), if (x,y) was already know, nothing happens
				  if (x,y) is not know, the class of variables X of x and the class Y of y are united so that 
				    the equivalence relation is maintained (y, y'), (x, x') -> (y',x')
      This might require the modification of some of the DFs (any pair of assignments (x',a) (y',b), a/=b is now invalidated)
    2) the modified DFs are enqueued
    3) the function processDFsQueue is called to recursively compute the consquences of the modifications
- addDF 
    1) adds a DF to a queue
    2) processDFsQueue calls pullDFs to see if this DF requires the modification of any of the existing DFs, if so, 
       pullDFs recursively computes the consquences

For efficiency, the structure is dynamically updated to maintain variable consitency:
1 Every variable class has a canonical member (the smallest value - variables are integers, remember). 
2 Every assignment all DFs in the valuation only use the canonical variable.
3 Every time two variable classes are united (e.g. [1,4,7] and [9,20]) a substitution (e.g. 1<-9) is applied to maintain 2)
(This is much more efficient then checking for variable equiality all the time.)
 -}
 
 
{- ******* Main ******* -}

type Var = Int
type Val = String

-- VarPartitions register variable equilities (contraints) ValutationAssignmentFrame registers the assigments.
data Valuation = Valuation VarPartition ValutationAssignmentFrame | INVALID deriving (Show)
  
addDF :: DisjunctiveFrame -> Valuation -> Valuation
addDF dF (Valuation varPartition vAF) = 
  let vars = getVarsVAF vAF
      substitutions = getSubstitutions vars varPartition
      updatedDF = applySubsititutionsDF substitutions dF
  in if updatedDF == []
	then INVALID
 else let
	  (_,resultingVAF) = processDFsQueue ([updatedDF],vAF)
      in if (elem [] resultingVAF)
	    then INVALID
     else (Valuation varPartition (resolveSingletonDFs resultingVAF))

addConstraints :: [Constraint] -> Valuation -> Valuation
addConstraints crs (Valuation partition vAF)
    = let
        (substitutions, newPartition) = addConstraintsAndComputeSubstitutions crs partition
        maybeVAF = applySubstitutions substitutions vAF
      in
        if (isJust maybeVAF)
        then Valuation newPartition (fromJust maybeVAF)
        else INVALID

        
{- ******* ValutationAssignments ******* -}

type ValutationAssignmentFrame = [DisjunctiveFrame]


{- ******* ValutationAssignmentFrame ******* -}

applySubstitutions :: [(Var, Var)] -> ValutationAssignmentFrame -> Maybe ValutationAssignmentFrame
applySubstitutions subs vAF
    = let
        processResult = processSubstitutions subs vAF
        (_, resultingVAF) = processDFsQueue processResult
      in
      if (elem [] resultingVAF)
      then Nothing
      else Just (resolveSingletonDFs resultingVAF)

processSubstitutions :: [(Var, Var)] -> ValutationAssignmentFrame -> (ValutationAssignmentFrame, ValutationAssignmentFrame)
processSubstitutions subs vAF
    = let
        (affectedAF, nonAffectedAF) = partitionDFsForVars (map (\(x,_) -> x) subs) vAF
      in
        ((applySubsititutionsVA subs affectedAF), nonAffectedAF)

partitionDFsForVars :: [Var] -> ValutationAssignmentFrame -> (ValutationAssignmentFrame, ValutationAssignmentFrame)
partitionDFsForVars vars = partition (affectedByVarsDF vars)

processDFsQueue :: (ValutationAssignmentFrame, ValutationAssignmentFrame)
                    -> (ValutationAssignmentFrame, ValutationAssignmentFrame)
processDFsQueue ([], vAF) = ([], vAF)
processDFsQueue ((headQueue:tailQueue), vAF)
  = let
        reducedDF = selfReduction (selfReduction headQueue vAF) tailQueue
        (newQueue, newVAF) = pullDFs reducedDF (tailQueue, vAF)
    in
        processDFsQueue (newQueue, reducedDF:newVAF)

pullDFs :: DisjunctiveFrame -> (ValutationAssignmentFrame, ValutationAssignmentFrame)
                            -> (ValutationAssignmentFrame, ValutationAssignmentFrame)
pullDFs _ ([], []) = ([], [])
pullDFs referenceDF (modifiedDF:tailModifiedDFs, [])
  = let
        (newTail, _) = pullDFs referenceDF (tailModifiedDFs,[])
    in
        ((removeIncompatibleCFs modifiedDF referenceDF):newTail, [])
pullDFs referenceDF (modifiedDFs, (nonModifiedDF:tailModifiedDFs))
  = let
        touchedDF = removeIncompatibleCFs nonModifiedDF referenceDF
        (newModifiedDFs, newTail) = pullDFs referenceDF (modifiedDFs, tailModifiedDFs)
    in
    if (length touchedDF) == (length nonModifiedDF)
    then (newModifiedDFs, (touchedDF:newTail))
    else ((touchedDF:newModifiedDFs), newTail)

selfReduction :: DisjunctiveFrame -> ValutationAssignmentFrame -> DisjunctiveFrame
selfReduction modifiableDF [] = modifiableDF
selfReduction modifiableDF (referenceDF:tail)
  = selfReduction (removeIncompatibleCFs modifiableDF referenceDF) tail

applySubsititutionsVA :: [(Var, Var)] -> ValutationAssignmentFrame -> ValutationAssignmentFrame
applySubsititutionsVA subs = map (applySubsititutionsDF subs)

resolveSingletonDFs :: ValutationAssignmentFrame -> ValutationAssignmentFrame
resolveSingletonDFs vAF
    = let (singletonDFs, rest) = partition singleton vAF
      in if (singletonDFs == []) then rest
      else (mergeSingletonDFs singletonDFs):rest

getVarsVAF :: ValutationAssignmentFrame -> [Var]
getVarsVAF dF = nub $ concat $ map getVarsDF dF


{- ******* DisjunctiveFrame ******* -}

type DisjunctiveFrame = [ConjunctiveFrame]

removeIncompatibleCFs :: DisjunctiveFrame -> DisjunctiveFrame -> DisjunctiveFrame
removeIncompatibleCFs modifiableFrame referenceFrame
  = filter (compatibleCFwDF referenceFrame) modifiableFrame

compatibleCFwDF :: DisjunctiveFrame -> ConjunctiveFrame -> Bool
compatibleCFwDF referenceDFrame cFrame = any (compatibleCFs cFrame) referenceDFrame

affectedByVarsDF :: [Var] -> DisjunctiveFrame -> Bool
affectedByVarsDF vars = any (affectedByVarsCF vars)

applySubsititutionsDF :: [(Var, Var)] -> DisjunctiveFrame -> DisjunctiveFrame
applySubsititutionsDF subs df = filter consistentCF $ map (applySubsititutionsCF subs) df

mergeSingletonDFs :: [DisjunctiveFrame] -> DisjunctiveFrame
mergeSingletonDFs list = foldl1 mergeTwoSingletonDFs list

mergeTwoSingletonDFs :: DisjunctiveFrame -> DisjunctiveFrame -> DisjunctiveFrame
mergeTwoSingletonDFs [cf1] [cf2] = [mergeTwoCFs cf1 cf2]
mergeTwoSingletonDFs [] [] = error "Trying to merge non singleton DFs"

getVarsDF :: DisjunctiveFrame -> [Var]
getVarsDF dF = nub $ concat $ map getVarsCF dF


{- ******* ConjunctiveFrame ******* -}

type ConjunctiveFrame = [Assignment]

consistentCF :: ConjunctiveFrame -> Bool
consistentCF = not.(hasDuplicates fst)

compatibleCFs :: ConjunctiveFrame -> ConjunctiveFrame -> Bool
compatibleCFs [] _ = True
compatibleCFs _ [] = True
compatibleCFs (x:xs) (y:ys)
  = (compatibleAssignments x y)
  && (compatibleCFs xs (y:ys))
  && (compatibleCFs (x:xs) ys)

affectedByVarsCF :: [Var] -> ConjunctiveFrame -> Bool
affectedByVarsCF vars = any (affectedByVarsAssignment vars)

applySubsititutionsCF :: [(Var, Var)] -> ConjunctiveFrame -> ConjunctiveFrame
applySubsititutionsCF subs cF = nub $ map (applySubsititutionsAssignment subs) cF

mergeTwoCFs :: ConjunctiveFrame -> ConjunctiveFrame -> ConjunctiveFrame
mergeTwoCFs cf1 cf2
  | compatibleCFs cf1 cf2 = nub $ cf1 ++ cf2
  | otherwise = error "Trying to merge non compatible CFs"

getVarsCF :: ConjunctiveFrame -> [Var]
getVarsCF cF = nub $ map fst cF

hasDuplicates :: (Eq b) => (a->b) -> [a] -> Bool
hasDuplicates _ [] = False
hasDuplicates _ [_] = False
hasDuplicates fun (x:xs) = (elemKey fun (fun x) xs) || (hasDuplicates fun xs)

elemKey :: (Eq b) => (a -> b) -> b -> [a] -> Bool
elemKey _ _ [] = False
elemKey fun elt (x:xs) = (elt == (fun x)) || (elemKey fun elt xs)


{- ******* Assignment ******* -}

type Assignment = (Var, Val)

affectedByVarsAssignment :: [Var] -> Assignment -> Bool
affectedByVarsAssignment vars (var, _) = elem var vars

applySubsititutionsAssignment :: [(Var, Var)] -> Assignment -> Assignment
applySubsititutionsAssignment [] a = a
applySubsititutionsAssignment ((oldVar,newVar):tail) (var, val)
  | oldVar == var = (newVar, val)
  | otherwise = applySubsititutionsAssignment tail (var, val)

compatibleAssignments :: Assignment -> Assignment -> Bool
compatibleAssignments (var1, val1) (var2, val2)
  | var1 == var2 = val1 == val2
  | otherwise = True

  
{- ******* VarPartition ******* -}

type VarClass = [Var]
type VarPartition = [VarClass]

type Constraint = (Var, Var)

consistentVarPartition :: VarPartition -> Bool
consistentVarPartition vP = let
				allVars = concat vP
			    in (length allVars) == (length (nub allVars)) --check that partitions do not have overlapp
  
varClass :: Var -> VarPartition -> VarClass
varClass var [] = var:[]
varClass var (x:tail)
  | elem var x = x
  | otherwise = varClass var tail

canonicalVar :: Var -> VarPartition -> Var
canonicalVar x p = minimum $ varClass x p

canonicalConstraint :: Constraint -> VarPartition -> Constraint
canonicalConstraint (var1, var2) partition = let
						cvar1 = canonicalVar var1 partition
						cvar2 = canonicalVar var2 partition
					     in
						((max cvar1 cvar2), (min cvar1 cvar2))

addressedBy :: Constraint -> VarClass -> Bool
addressedBy (var1, var2) c = (elem var1 c) || (elem var2 c)

addConstraint :: Constraint -> VarPartition -> VarPartition
addConstraint (var1, var2) p
    | (canonicalVar var1 p) == (canonicalVar var2 p) = p
    | otherwise
        = let
	    (varPartition, restPartition) = partition (addressedBy (var1, var2)) p
        in ((varClass var1 varPartition) ++ (varClass var2 varPartition)):restPartition


addConstraintsAndComputeSubstitutions :: [Constraint] -> VarPartition -> ([(Var,Var)], VarPartition)
addConstraintsAndComputeSubstitutions crs partition
  = let
        vars = (extractVars crs)
        newPartition = cascade addConstraint crs partition
        substitutions = (filter (\(a,b) -> a/=b)
                            (nub (map (\x -> ((canonicalVar x partition), (canonicalVar x newPartition))) vars)))
    in
        (substitutions, newPartition)

extractVars :: [Constraint] -> [Var]
extractVars []=[]
extractVars ((a,b):tail) = a:b:(extractVars tail)

getSubstitutions :: [Var] -> VarPartition -> [(Var, Var)]
getSubstitutions vars vp = getSubstitutions' (nub vars) vp

getSubstitutions' :: [Var] -> VarPartition -> [(Var, Var)]
getSubstitutions' [] _ = []
getSubstitutions' (var:varTail) vp = 
  let cvar = canonicalVar var vp 
  in if cvar == var
	then getSubstitutions' varTail vp
	else (var,cvar):(getSubstitutions' varTail vp)

	
{- ******* Auxiliary functions ******* -}

mergeSingletons :: [[a]] -> [[a]]
mergeSingletons list = let (singletons, rest) = partition singleton list in (concat singletons):rest

singleton :: [a] -> Bool
singleton [_] = True
singleton _ = False

cascade :: (b->a->a) -> [b] -> a -> a
cascade _ [] arg = arg
cascade fun (x:xs) arg = cascade fun xs (fun x arg)

{- testcases:
:{
processDFsQueue
([[[(1,102)]]],
[[[(1,101),(2,102)], [(2,103)]],
 [[(2,102),(3,103)], [(3,104)]],
 [[(3,103),(4,104)], [(4,105)]]])
 :}

:{
processDFsQueue
(
[[[(1,102),(4,104)],[(1,102),(4,105)]]],
[[[(1,101),(2,102)], [(2,103)]],
 [[(2,102),(3,103)], [(3,104)]],
 [[(3,103),(4,104)], [(4,105)]]])
 :}

:{
processDFsQueue
([[[(1,102)]]],
[[[(1,101),(2,102)], [(2,103)]],
 [[(2,102),(3,103)], [(3,104)]],
 [[(3,103),(4,104)], [(4,105),(1,102)]]])
 :}

addDF [[(3,103)]] $ addDF [[(1,101),(2,102)]] $ Valuation [] []
-> Valuation [] [[[(3,101),(1,101),(2,102)]]]
addConstraints [(5,3)] $ Valuation [] [[[(3,101),(1,101),(2,102)]]]
-> Valuation [[5,3]] [[[(3,101),(1,101),(2,102)]]]
addConstraints [(1,3)] $ Valuation [[5,3]] [[[(3,101),(1,101),(2,102)]]]
-> Valuation [[1,5,3]] [[[(1,101),(2,102)]]]
addConstraints [(1,2)] $ Valuation [[5,3]] [[[(3,101),(1,101),(2,102)]]]
-> INVALID 
addConstraints [(9,2)] $ Valuation [] [[[(1,101),(2,102)], [(2,103)]], [[(2,102),(3,103)], [(3,104)]], [[(3,103),(4,104)], [(4,105)]]]
-> Valuation [[9,2]] [[[(1,101),(2,102)],[(2,103)]],[[(2,102),(3,103)],[(3,104)]],[[(3,103),(4,104)],[(4,105)]]]
addConstraints [(1,2)] $ Valuation [] [[[(1,101),(2,102)], [(2,103)]], [[(2,102),(3,103)], [(3,104)]], [[(3,103),(4,104)], [(4,105)]]]
-> Valuation [[1,2]] [[[(4,105),(3,104),(1,103)]]]
addConstraints [(1,2)] $ Valuation [] [[[(1,101),(2,102)], [(2,103)]], [[(2,102),(3,103)], [(3,104)]], [[(3,103),(4,104)], [(1,102)]]]
-> INVALID

addConstraints [(1,10)] $ addDF [[(1,101),(2,102)],[(2,103)]] $ addDF [[(10,110),(15,115)]] $ Valuation [] []

-}