import Valuation
import Data.Maybe
import Data.List

{-- testing --}

orthNodes = [(Node "orthNode" [] [("orth",1)] []),(Node "orthNode" [] [("orth",2)] [])]  
testNodes = [(Node "" [] [("syncat", 10), ("referent",11)] [orthNodes!!0]), (Node "" [] [("syncat",12), ("referent",13)] [orthNodes!!1])] 
testValuation = (Valuation [] [[[(1,"the"),(2,"NAO"),(10,"DetCat"),(12,"NounCat")]]])
testConstruction1 = 
 (Construction 
  "NP-CXN" 
  ["Det", "Noun"]
  ["Det", "Noun"]
  [(["Det", "referent"], 20), (["Det", "syncat"], 21), (["Noun", "referent"], 22), (["Noun", "syncat"], 23)] 
  [("referent",30),("syncat",31)]
  (Valuation [[20,30,22]] [[[(21,"DetCat"), (22, "NounCat"), (31,"NPCat")]]]))
testConstruction1b = 
 (Construction 
  "NP-CXN" 
  ["Det", "Noun"]
  ["Det", "Noun"]
  [(["Det", "referent"], 20), (["Det", "syncat"], 21), (["Noun", "referent"], 20), (["Noun", "syncat"], 23)] 
  [("referent",20),("syncat",31)]
  (Valuation [] [[[(21,"DetCat"), (22, "NounCat"), (31,"NPCat")]]]))
testConstruction2 = 
 (Construction 
  "NP-CXN2" 
  ["Det", "Noun"]
  ["Det", "Noun"]
  [(["Det", "referent"], 20), (["Det", "syncat"], 21), (["Det", "number"], 24), (["Noun", "referent"], 22), (["Noun", "syncat"], 23)] 
  [("referent",30),("syncat",31)]
  (Valuation [[20,30,22]] [[[(21,"DetCat"), (22, "NounCat"), (22, "singular"), (31,"NPCat")]]]))

assembledConstructionCorrect = preAssembleNode testNodes testConstruction1
assembledConstructionFailsOnFeatureMatch = preAssembleNode testNodes testConstruction2
assembledConstructionFailsOnAddConstructionConstraints = preAssembleNode [testNodes!!1,testNodes!!0] testConstruction1
{-
*Main> featuresMatch testConstruction1 assembledConstructionCorrect 
True
*Main> featuresMatch testConstruction1 assembledConstructionFailsOnAddConstructionConstraints  
True
*Main> featuresMatch testConstruction2 assembledConstructionFailsOnFeatureMatch 
False
*Main> computeAdditionalConstraints testConstruction1 assembledConstructionCorrect 
[(11,20),(10,21),(13,22),(12,23)]
*Main> computeAdditionalConstraints testConstruction1 assembledConstructionFailsOnFeatureMatch  
[(11,20),(10,21),(13,22),(12,23)]
*Main> computeAdditionalConstraints testConstruction2 assembledConstructionFailsOnAddConstructionConstraints 
[(13,20),(12,21),(*** Exception: Feature "number" does not exist in node "Det"

-}




type Label = String
stringToLabel :: String -> Label
stringToLabel = id

type Identifier = [Label]
type SpecificationFrame = ([(Identifier,Identifier)],[[[(Var, Val)]]])

data Construction = Construction {constructionName :: String,
				   constructionConstituents :: [Label],
				   constructionConstituentPattern :: [Label],
				   constructionExternals :: [(Identifier,Var)],
				   constructionFeatures :: [(Label, Var)],
				   constructionValuation :: Valuation} deriving (Show)
				   

data EvaluationForest = EvaluationForest [Node] Valuation



{-- Matching --}
applyConstruction :: Construction -> ([Node], Valuation) -> (Node, Valuation)
applyConstruction construction (nodes, valuation) 
  = let preAssembledNode = preAssembleNode nodes construction
    in if (featuresMatch construction preAssembledNode)
	   then let 
	     additionalConstraints = computeAdditionalConstraints construction preAssembledNode
	     mergedValuation = mergeDisjointValuations valuation (constructionValuation construction)
	 in (preAssembledNode, (addConstraints additionalConstraints mergedValuation))
    else (preAssembledNode, INVALID)
	

computeAdditionalConstraints :: Construction -> Node -> [Constraint]
computeAdditionalConstraints construction node = map (\(identifier, var) -> ((getVarForIdentifier node identifier), var)) (constructionExternals construction)

featuresMatch :: Construction -> Node -> Bool
featuresMatch construction node = all (containsIdentifier node) (map fst (constructionExternals construction))

mergeDisjointValuations :: Valuation -> Valuation -> Valuation
mergeDisjointValuations (Valuation varPartition1 vAF1) (Valuation varPartition2 vAF2) 
  = Valuation (varPartition1 ++ varPartition2) (resolveSingletonDFs (vAF1 ++ vAF2))

type Feature = (Label, Var) 
data Node = Node {nodeLabel :: Label, 
		  nodeConstituentPattern :: [Label],
		  nodeFeatures :: [(Label, Var)], 
		  nodeChildren :: [Node]} deriving (Eq, Show)

setLabel :: Node -> Label -> Node
setLabel (Node _ p f c) label = (Node label p f c)

setLabels :: [Node] -> [Label] -> [Node]
setLabels nodes labels 
  | (length nodes) == (length labels) = zipWith setLabel nodes labels
  | otherwise = error "number of labels does not match number of nodes"

  
preAssembleNode :: [Node] -> Construction -> Node
preAssembleNode nodes construction = (Node 
					"tmpHead"
					(constructionConstituentPattern construction) 
					(constructionFeatures construction)
					(setLabels nodes (constructionConstituents construction)))

  
{-- ********* resolve Identifiers ********* --}
  
containsIdentifier :: Node -> Identifier -> Bool
containsIdentifier _ [] = error "Empty Identifier"
containsIdentifier node [l] = elemKey fst l (nodeFeatures node)
containsIdentifier node (l:rest) = let maybeChild = find (\n -> (nodeLabel n)==l) (nodeChildren node) 
				   in if (maybeChild == Nothing)
				    then False
	else containsIdentifier (fromJust maybeChild) rest
  

getVarForIdentifier :: Node -> Identifier -> Var
getVarForIdentifier _ [] = error "Empty Identifier"
getVarForIdentifier node [x] 
  = snd $ locateOrFail (\ (y,_) -> x==y) 
		  (nodeFeatures node) 
		  ("Feature " ++ (show x) ++ " does not exist in node " ++ (show (nodeLabel node)))  
getVarForIdentifier node (l:rest) 
  = getVarForIdentifier 
  (locateOrFail 
    (\n -> (nodeLabel n) == l) 
    (nodeChildren node) 
    ("Node " ++ (show node) ++ " does not have a child named " ++ (show l))) 
  rest
  
  
{-- ********* Aux ********** --}

valueOrFail :: Maybe a -> String -> a
valueOrFail Nothing error_msg = error error_msg
valueOrFail (Just value) _ = value

locateOrFail :: (a->Bool)->[a]->String->a
locateOrFail predicate list error_msg = valueOrFail (find predicate list) error_msg


{-- ********* Printing ********** --}

ppApplicationResult :: (Node, Valuation) -> IO ()
ppApplicationResult = putStr.toStringApplicationResult

toStringApplicationResult :: (Node, Valuation) -> String
toStringApplicationResult (node, valuation) = "Application Result: \n" ++ (toStringNode node 0) ++ (toStringValuation valuation)

ppNode :: Node -> IO ()
ppNode node = putStr $ toStringNode node 0

toStringNode :: Node -> Int ->  String
toStringNode node indent = let leadingSpace = take indent $ repeat ' '
			   in leadingSpace ++ "Node: " ++ (show (nodeLabel node)) ++ "\n" ++
			      leadingSpace ++ "Constituent pattern: " ++ (show (nodeConstituentPattern node)) ++ "\n" ++
			      leadingSpace ++ "Features: " ++ (show (nodeFeatures node)) ++ "\n" ++
			      leadingSpace ++ "Constituents: \n" ++
			      concat (map (\child -> toStringNode child (indent + 2)) (nodeChildren node))
			      
ppValuation :: Valuation -> IO ()
ppValuation val = putStr $ toStringValuation val

toStringValuation :: Valuation -> String
toStringValuation (Valuation varcluster vAF) = "Valuation: " ++ (show varcluster) ++ "\n" ++ (toStringVAF vAF) ++ "\n"
toStringValuation INVALID = "INVALID\n"

toStringAssginment :: Assignment -> String
toStringAssginment (var,val) = (show var) ++ "->" ++ (show val)
					 
toStringCF :: ConjunctiveFrame -> String
toStringCF cf = "{" ++ (glueStringsWith (map toStringAssginment cf) ",") ++ "}"

toStringDF :: DisjunctiveFrame -> String
toStringDF df = "[" ++ (glueStringsWith (map toStringCF df) "-OR-") ++ "]"

toStringVAF :: ValutationAssignmentFrame -> String
toStringVAF vAF = (glueStringsWith (map toStringDF vAF) "--AND--\n")

glueStringsWith :: [String] -> String -> String
glueStringsWith [] _ = []
glueStringsWith (x:[]) _ = x
glueStringsWith (x:xs) string = x ++ string ++ (glueStringsWith xs string)



  {-			
  (EvaluationTree
  [(Node "NP" 
  (Pattern ["Det","N"]) 
  (Features [("ref", 10),("number", 11)])  
  (Children [(Node "Det" 
  (Pattern []) 
  (Features [("orth",1),("ref",2),("givenness",3),("number",4),("cat",5)])
  (Children [])), 
  (Node "N" 
  (Pattern []) 
  (Features [("orth",6),("ref",7),("number",8),("cat",9),("object-class",12)])
  (Children []))]))]
  (Valuation [[1],[2,7,10],[3],[4,8,11],[5],[6],[9]] [[[(1,"the"), (3,"true"), (4,"singular"), (5,"determiner"), (6,"Nao"), (9,"noun"), (12, "robot")]]]))
  -}
  
  {-
  construction NP (ReferentialExpression):
  constituents:
  d:Det, n:N
  form:
  Det.syn-cat = "Det"
  Det meets N
  meaning:
  Det.sem-cat = "Det"
  Det.ref = N.ref
  
  
  ["the", "NAO", "can", "talk"]
  ["can", "the", "nao", "talk"]
  -}
  
  