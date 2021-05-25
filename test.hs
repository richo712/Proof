module Test (Sentence(Arb,Vld,Op0,Op1,Op2,Op3,Opn),SideCon,Rule(Rule,RuleP,NoOp),PT(PT,PTA),Forest,add2PrfS,add2Prf,add2PrfRmv,crtPrf,spread,spreadPrf
	,conSolved,isSolved4,isPartSolution,isSolution,dumbComp,smartCnnt,Proof,Logic,makeNewRule,prune,pruneN,pruneTree,PreSent(PS),
	Pass(Sen,Ref,Ant,Con),Value(Value),getTree,cnnct,getAProof,rmvMaybe,getVldData,toBuss,getProof,vals,spreadAll,root,chd,rmvByCon) where 

import System.IO
import Data.List

data Value = Value Int Int
	deriving(Show,Eq,Ord)

te = Value 0 1
dt = [1]

vldData :: Show a => Value -> [a] -> Maybe a 
vldData (Value x y) l 
	| y < 0 = Nothing
	| y >= length l = Nothing
	| otherwise = Just (l!!y)

getVldData :: Show a => Sentence -> [a] -> Maybe a
getVldData (Vld x) l = vldData x l
getVldData _ _ = Nothing
 

data Sentence = Arb Char
		| Frs Char
		| Vld Value 
		| Op0 String --Will be in there all ready and has all you could need in the way of sentences				-- May need add a way to deal with variables
		| Op1 String Sentence
		| Op2 String Sentence Sentence
		| Op3 String Sentence Sentence Sentence
		| Opn String [Sentence]
		deriving(Ord)
	
	
vals :: Int -> Int -> Sentence
vals a b = Vld (Value a b) 

allChar = ['A' .. 'Z']
allArb = map Arb allChar

instance Show Sentence where
	show(Arb x) = show(x)
	show(Frs x) = show(x) ++ "h"
	show(Vld x) = show(x)
	show(Op0 x) = show(x)
	show(x)     = sentShow (cngOp x)
	
sentShow :: Sentence -> String
sentShow (Opn x l) = show(x) ++ show(l)
	
instance Eq Sentence where 
	(==) x y = sentEq (cngOp x) (cngOp y) 
			
sentEq :: Sentence -> Sentence -> Bool
sentEq (Arb c) (Arb d) 		= c == d 			
sentEq (Vld v) (Vld y) 		= v == y
sentEq (Opn x l) (Opn y m)	= x == y && l == m 	
sentEq _ _ = False		


data PreSent = PS Sentence [Sentence] -- Just giving this name to make the coding a little easier
	deriving(Show,Eq)
getRef :: PreSent -> Sentence
getRef (PS s _) = s
getAsmp :: PreSent -> [Sentence]
getAsmp (PS _ l) = l

type SideCon = [Sentence] -> Bool

data Rule 	= Rule  String [Sentence]    [SideCon] Sentence 
			| RuleP String [PreSent] [SideCon] Sentence 
			| NoOp -- Naming so it can be put in as the type of a function Alter rules lower down

instance Eq Rule where 
	(==) (Rule nme1 a1 _ s1) (Rule nme2 a2 _ s2) = nme1 == nme2 && a1 == a2 && s1 == s2
	(==) (RuleP nme1 a1 _ s1) (RuleP nme2 a2 _ s2) = nme1 == nme2 && a1 == a2 && s1 == s2
	(==) (NoOp) (NoOp) = True
	(==) _ _ = False

instance Show Rule where 
	show(Rule s _ _ _) = show(s) 
	show(RuleP s _ _ _) = show(s) 
	show(NoOp) = "NoOp"

data PT a = PT Sentence Rule [PT Sentence]
	| PTA Sentence Rule [Sentence] [PT Sentence]
	deriving(Show,Eq)

type Forest = [PT Sentence]

type Logic = [Rule]

data Pass = Sen Sentence
	| Ant Int
	| Ref Int
	| Con
	deriving(Show)

getTree :: Proof -> Pass -> PT Sentence
getTree  _ 	(Sen x)				= PT x NoOp []
getTree  (Proof a _ _) (Ant x) 	= PT (a!!x) NoOp []
getTree  (Proof _ _ f) (Ref x)  = f!!x
getTree  (Proof _ c _)  Con  	= PT c NoOp []  

root :: PT Sentence -> Sentence
root (PT x _ _) = x
root (PTA x _ _ _) = x
rootIs :: Sentence -> PT Sentence -> Bool
rootIs s r = root r == s 
getRule :: PT Sentence -> Rule
getRule (PT _ rle _) = rle
getRule (PTA _ rle _ _) = rle
chd :: PT Sentence -> [PT Sentence]
chd (PT _ _ x) = x
chd (PTA _ _ _ x) = x
	
add2Frst :: Proof -> PT Sentence -> Proof 
add2Frst (Proof ant con frst) tre = Proof ant con (frst ++ [tre])   
add2Frst' :: Proof -> PT Sentence -> Proof 
add2Frst' (Proof ant con frst) tre = Proof ant con ([tre] ++ frst)   

ins :: Pass -> [Pass] -> [Pass]
ins (Ref x)  ((Ref y):ys) 
	| x <= y = (Ref x) : ((Ref y):ys) 
	| otherwise = (Ref y) : (ins (Ref x) ys) 
ins x [] = [x]

rmvUsd :: Proof -> [PT Sentence] -> Proof 
rmvUsd (Proof ant sen frst) (x:xs) = rmvUsd (Proof ant sen (delete x frst)) xs
rmvUsd prf [] = prf   

rmvByCon :: Proof -> Sentence -> Proof
rmvByCon (Proof a c (x:xs)) s 
	| root x == s = rmvByCon (Proof a c xs) s
	| otherwise   = add2Frst' (rmvByCon (Proof a c xs) s) x 
rmvByCon (Proof a c []) s = (Proof a c []) 

findSent :: Proof -> Sentence -> [PT Sentence]
findSent (Proof a c frst) s = findSent'  s frst
findSent' :: Sentence -> [PT Sentence] -> [PT Sentence]
findSent' s (x:xs) 
	| s == root x 	= [x] ++ (findSent' s xs) 
	|otherwise		= (findSent' s xs) 
findSent' s [] = []

isPartSolution :: Proof -> Bool 
isPartSolution p = dumbComp p == p

dumbComp  :: Proof -> Proof
dumbComp p 
	| posP /= Nothing 	= rmvMaybe posP
	| otherwise 		= p
	where
	posP = dumbComp' (getSolved4 p) p
dumbComp' :: [Sentence] -> Proof -> Maybe Proof 
dumbComp' a p 
	| conSolved newP = Just newP
	| newA == a = Nothing
	| otherwise = dumbComp' newA newP
	where 
	newP = smartCnnt p
	newA = getSolved4 newP

smartCnnt  :: Proof -> Proof
smartCnnt p = foldr spreadPrf p (getSolved4 p) 

updateRef :: PT Sentence ->  Proof -> Int -> Proof
updateRef tree (Proof a c frst) n = (Proof a c (updateFrst tree n frst))
updateFrst :: PT Sentence -> Int -> Forest -> Forest
updateFrst tree n (x:xs)
	| 0 == n = tree:xs
	| otherwise = x : (updateFrst tree (n - 1) xs)
updateFrst _ _ [] = []

pruneN :: Pass -> Proof -> Proof
pruneN (Ref x) p = updateRef (pruneTree p (getTree p (Ref x))) p x


pruneTree :: Proof -> PT Sentence -> PT Sentence
pruneTree (Proof a c frst) (PT s r l)  --TODO Prune and then see what else can be done while writing conclusion and the rest of the design 
	| s `elem` a = PT s NoOp [] 
	| otherwise = PT s r (map (pruneTree (Proof a c frst)) l)

prune :: Proof -> Proof -- To prune after [Sentence]
prune (Proof a c frst) = (Proof a c (map (pruneTree (Proof a c frst)) frst))

getAllSent  :: Proof -> [Sentence]
getAllSent (Proof _ _ frst) = getAllSent' frst []
getAllSent' :: [PT Sentence] -> [Sentence] -> [Sentence]
getAllSent' (x:xs) l 
	| root x `elem` l 	= getAllSent' ((chd x) ++ xs) l
	|otherwise 			= getAllSent' xs ((root x):l)
getAllSent' [] l = l

getSolved4  :: Proof -> [Sentence]
getSolved4 p = filter (isSolved4 p) (getAllSent p)

makeNewRule :: String -> [SideCon] -> Proof -> Rule
makeNewRule name side (Proof a c frst)
	| conSolved (Proof a c frst) = (Rule name a side c)
	| otherwise = NoOp

conSolved :: Proof -> Bool  
conSolved prf = isSolved4 prf (root (getTree prf (Con)))
isSolved4 :: Proof -> Sentence -> Bool  
isSolved4 prf s = getAProof prf s /= Nothing

getProof :: Proof -> Maybe (PT Sentence)
getProof (Proof a c f) = getAProof (Proof a c f) c

getAProof :: Proof -> Sentence -> Maybe (PT Sentence) -- Make sure to make a form a proof
getAProof prf s = getAProof' prf (findSent prf s)
getAProof' :: Proof -> [PT Sentence] -> Maybe (PT Sentence) 
getAProof' prf (x:xs)
	| isSolution prf x 	= Just x
	| otherwise 		= getAProof' prf xs
getAProof' _ [] 		= Nothing


isSolution :: Proof -> PT Sentence -> Bool
isSolution  (Proof a c f) (PT s rle tre) 
	| any (== root x) a = True
	| getRule x == NoOp	= False
	| chd x == [] = True
	| otherwise 		= and (map (isSolution (Proof a c f)) (chd x))
	where 
	x = (PT s rle tre)
	
isSolution  (Proof a c f) (PTA s rle amp tre) 
	| any (== root x) a = True
	| getRule x == NoOp	= False
	| chd x == [] = True
	| otherwise 		= and (map (isSolution (Proof (a ++ amp) c f)) (chd x))
	where 
	x = (PTA s rle amp tre)

data Proof = Proof [Sentence] Sentence Forest
	deriving(Eq)
			
data Proof' = Fst [Sentence] Forest Int
			| Scd Forest Int
	
instance Show Proof where 
	show(Proof ant sen frst) = "Con  :  " ++ show(sen) ++ "\n" ++ show(Fst ant frst 0)

instance Show Proof' where 
	show(Fst (x:xs) frst cur)  	= "Ant " ++ show(cur) ++ ":  " ++ show(x) ++ "  " ++ show(Fst xs frst (cur + 1))
	show(Fst [] frst _) 		= show(Scd frst 0)
	show(Scd (x:xs) cur)			= "\nRef " ++ show(cur) ++ ":\n" ++ show(x) ++ show(Scd xs (cur + 1))
	show(Scd [] _)				= ""
	
crtPrf :: [Sentence] -> Sentence -> Proof
crtPrf a s = Proof a s []

add2PrfS :: Proof -> Rule -> [Sentence] -> Sentence -> Proof
add2PrfS p r a s = add2Prf p r (map Sen a) s 

add2Prf :: Proof -> Rule -> [Pass] -> Sentence -> Proof -- Needs fixing
add2Prf prf rle pss s 
	| a == Nothing = prf
	where
	a = apRle rle (map root (map (getTree prf) pss)) s
add2Prf prf (Rule w x y z) pss s = add2Prf' prf (Rule w x y z) pss s (TInfo a c)
	where
	(TInfo a c) = rmvMaybe (apRle (Rule w x y z) (map root (map (getTree prf) pss)) s)
add2Prf prf (RuleP w x y z) pss s = add2Prf' prf (RuleP w x y z) pss s (TInfo a c)
	where
	(TInfo a c) = rmvMaybe (apRle (RuleP w x y z) (map root (map (getTree prf) pss)) s)
	
add2Prf' :: Proof -> Rule -> [Pass] -> Sentence -> TInfo -> Proof
add2Prf' prf (Rule w x y z) pss ogS (TInfo a n)
	| l /= Nothing = add2Frst prf (PT ogS rle (map (getTree prf) pss)) 
	| otherwise = prf
	where 
	rle = (Rule w x y z)
	l = swpFrs ogS [[n]]
add2Prf' prf (RuleP w x y z) pss ogS (TInfo a c)
	| l /= Nothing = add2Frst prf (PT ogS rle (addAsm prf pss (mp (rmvMaybe l) a))) 
	| otherwise = prf
	where 
	rle = (RuleP w x y z)
	l = swpFrs ogS ([c]:(map getAsmp a)) 
mp :: [[Sentence]] -> [PreSent] -> [PreSent]
mp (se:ses) (an:ans) 
	| length ses > length ans = mp ses (an:ans) 
	| otherwise = (PS (getRef an) se):(mp ses ans) 
	
conPTA :: [Sentence] -> PT Sentence -> PT Sentence
conPTA l (PT a r frst) = PTA a r l frst
addAsm :: Proof -> [Pass] -> [PreSent] -> [PT Sentence]
addAsm prf (x:xs) ((PS _ []):ys) = (getTree prf x):addAsm prf xs ys 
addAsm prf (x:xs) ((PS a l):ys) = (conPTA l (getTree prf x)):addAsm prf xs ys
addAsm _ [] _ = []
	
add2PrfRmv :: Proof -> Rule -> [Pass] -> Sentence -> Proof
add2PrfRmv prf rle pss s = rmvUsd (add2Prf prf rle pss s) (map (getTree prf) pss)

sprdDel :: Pass -> Proof -> Proof
sprdDel pss (Proof a c frst) = rmvUsd (Proof a c (spread' s frst)) [s]
	where s = getTree (Proof a c frst) pss

spreadPrf :: Sentence -> Proof -> Proof 
spreadPrf s (Proof a c frst) 
	| prvS /= Nothing = (Proof a c (spread' (rmvMaybe prvS) frst)) 
	| otherwise = prf
	where 
		prf = (Proof a c frst)
		prvS = (getAProof prf s)

spreadAll :: Proof -> Proof
spreadAll' :: Proof -> [Sentence] -> [Sentence]
spreadAll p = foldr spread p (spreadAll' p [])
spreadAll' (Proof a c (f:fs)) l
	|r `elem` l 			=  	spreadAll' (Proof a c (fs)) l
	|otherwise              =   spreadAll' (Proof a c (fs)) (r:l)
	where r = root f 
spreadAll' (Proof a c []) l = l 

spread :: Sentence ->  Proof -> Proof
spread s (Proof a c frst) = (Proof a c (foldr spread' frst (filter (rootIs s) frst)))
spread' :: PT Sentence -> Forest ->  Forest
spread' s (x:xs) 
	| root x == root s = x : (spread' s xs) 
	| otherwise = add2Leaf s x : (spread' s xs)
spread' _ []  = []


cnnct :: Proof -> Pass -> Pass -> Proof 
cnnct (Proof a c frst) to frm 
	| (any (== toT) frst) && (any (== frmT) frst) = add2Frst' (rmvUsd prf [toT]) (add2Leaf frmT toT)
	| otherwise 	= prf 
	where 	
		prf = (Proof a c frst)
		toT = getTree prf to
		frmT = getTree prf frm
	
add2Leaf :: PT Sentence -> PT Sentence -> PT Sentence
add2Leaf frm  (PT r rle brh) 
	| brh == [] && r == root frm 						= (PT r (getRule frm) (chd frm))
	| brh == [] 										= (PT r rle [])
	| otherwise 										= (PT r rle (map (add2Leaf frm) brh))
add2Leaf frm  (PTA r rle a brh) 
	| brh == [] && r == root frm 						= (PTA r (getRule frm) a (chd frm))
	| brh == [] 										= (PTA r rle a [])
	| otherwise 										= (PTA r rle a (map (add2Leaf frm) brh))

-- Begin Rule Application
data AsgnArb = AsgnArb Sentence Sentence
	deriving(Show,Eq)
	
data TInfo = TInfo [PreSent] Sentence
	deriving(Show,Eq)
	
data AppRtn = AppRtn Sentence [AsgnArb]
	deriving(Show,Eq)

cngOp :: Sentence -> Sentence
cngOp (Op0 x) = Opn x []
cngOp (Op1 x s1) = Opn x (s1:[])
cngOp (Op2 x s1 s2) = Opn x (s1:s2:[])
cngOp (Op3 x s1 s2 s3) = Opn x (s1:s2:s3:[])
cngOp s = s 

rmvMaybe :: Maybe a -> a
rmvMaybe (Just s) = s

deleteAll :: Eq a => [a] -> [a] -> [a]
deleteAll (x:xs) lst = deleteAll xs (delete x lst)
deleteAll [] lst = lst

getArbInSent :: Sentence -> [Sentence] 
getArbInSent (Arb a) = [(Arb a)]
getArbInSent (Vld a) = []
getArbInSent (Opn r (x:xs)) = (getArbInSent x) ++ (getArbInSent (Opn r xs))
getArbInSent (Opn _ []) = []
getArbInSent a = getArbInSent (cngOp a)  

getFresh4 :: Sentence -> [AsgnArb] -> AppRtn
getFresh4 s a = getFresh4' s a a allArb
getFresh4' :: Sentence -> [AsgnArb] -> [AsgnArb] -> [Sentence] -> AppRtn
getFresh4' s a ((AsgnArb _ x):xs) lst = getFresh4' s a xs (deleteAll (getArbInSent x) lst)
getFresh4' s a [] lst = AppRtn (lst!!0) ((AsgnArb s (lst!!0)):a)

swpFrs  :: Sentence -> [[Sentence]] -> Maybe [[Sentence]]
swpFrs og new  
	| asgn /= Nothing = Just (map (map (makeConAnt asgn)) new')
	| otherwise = Nothing
	where 
	new' = (map (map (swpFrs')) new)
	asgn = essEq ((new'!!0)!!0) og (Just [])
	
makeConAnt :: Maybe [AsgnArb] -> Sentence -> Sentence
makeConAnt l s = rmvFrs' (convertArb l s)
	
swpFrs' :: Sentence -> Sentence
swpFrs' (Frs x) = Arb x
swpFrs' (Arb x) = Frs x
swpFrs' (Op0 x) = (Op0 x)
swpFrs' (Op1 x s) = (Op1 x (swpFrs' s))
swpFrs' (Op2 x s1 s2) = (Op2 x (swpFrs' s1) (swpFrs' s2))
swpFrs' (Op3 x s1 s2 s3) = (Op3 x (swpFrs' s1) (swpFrs' s2) (swpFrs' s3))
swpFrs' (Opn x l) = (Opn x (map swpFrs' l))
swpFrs' (Vld x) = Vld x

rmvFrs :: [Sentence] -> [Sentence]
rmvFrs l = map rmvFrs' l

rmvFrs' :: Sentence -> Sentence
rmvFrs' (Frs x) = Arb x
rmvFrs' (Arb x) = Arb x
rmvFrs' (Op0 x) = (Op0 x)
rmvFrs' (Op1 x s) = (Op1 x (rmvFrs' s))
rmvFrs' (Op2 x s1 s2) = (Op2 x (rmvFrs' s1) (rmvFrs' s2))
rmvFrs' (Op3 x s1 s2 s3) = (Op3 x (rmvFrs' s1) (rmvFrs' s2) (rmvFrs' s3))
rmvFrs' (Opn x l) = (Opn x (map rmvFrs' l))
rmvFrs' (Vld x) = Vld x


convertArb :: Maybe [AsgnArb] -> Sentence -> Sentence
convertArb' :: [AsgnArb] -> Sentence -> AppRtn
convertArb (Just a) s = newS 
	where 
	(AppRtn newS newA) = convertArb' a s
	
convertArb' a (Arb x) 
	| n /= Nothing = AppRtn (rmvMaybe n) a
	| otherwise = AppRtn (Frs x) a
	where 
	n = (getArbS (Arb x) a)
	
convertArb' a (Frs x) = AppRtn (Frs x) a 
	
convertArb' a (Op1 x s) = AppRtn (Op1 x newS) newA
	where 
	(AppRtn newS newA) = convertArb' a s
	
convertArb' a (Op2 x s1 s2) = AppRtn (Op2 x newS1 newS2) newA2
	where 
	(AppRtn newS1 newA1) = convertArb' a s1
	(AppRtn newS2 newA2) = convertArb' newA1 s2
	
convertArb' a (Op3 x s1 s2 s3) = AppRtn (Op3 x newS1 newS2 newS3) newA3
	where 
	(AppRtn newS1 newA1) = convertArb' a s1
	(AppRtn newS2 newA2) = convertArb' newA1 s2
	(AppRtn newS3 newA3) = convertArb' newA2 s3
	
convertArb' a (Opn y1 (x:xs)) = AppRtn (Opn y1 (s:l)) finA
	where 
	(AppRtn (Opn y2 l) newA) = convertArb' a (Opn y1 xs) 
	(AppRtn s finA) = (convertArb' newA x)
	
convertArb' a s  = AppRtn s a

getArbS :: Sentence -> [AsgnArb] -> Maybe Sentence
getArbS a ((AsgnArb arb s):xs) 
	| arb == a = Just s
	| otherwise = getArbS a xs
getArbS a [] = Nothing

essEqOp :: [Sentence] -> [Sentence] -> Maybe [AsgnArb] -> Maybe [AsgnArb]
essEqOp (x:xs) (y:ys) (Just a) 
	| toPass == Nothing = Nothing 
	| otherwise = essEqOp xs ys toPass 
	where toPass = essEq x y (Just a)
essEqOp (x:xs) [] a = Nothing
essEqOp [] (y:ys) a = Nothing
essEqOp [] [] a = a 

essEq :: Sentence -> Sentence -> Maybe [AsgnArb] -> Maybe [AsgnArb] -- Sen of rule, Sen of [Sentence], Assigned arbs so far
essEq x y asgn = essEq' (cngOp x) (cngOp y) asgn
essEq' :: Sentence -> Sentence -> Maybe [AsgnArb] -> Maybe [AsgnArb] -- Sen of rule, Sen of [Sentence], Assigned arbs so far
essEq' (Arb x) senA (Just asgn) 
	| assigned == Nothing = Just (((AsgnArb (Arb x) senA)):asgn)
	| assigned == (Just senA) = Just asgn
	| otherwise = Nothing
	where assigned = getArbS (Arb x) asgn
essEq' (Vld x) (Vld y) asgn
	| x == y = asgn
	| otherwise = Nothing
essEq' (Frs x) (Arb y) asgn
	| x == y = asgn
	| otherwise = Nothing
essEq' (Opn x l) (Opn y m) a
	| x == y && length l == length m = essEqOp l m a
	|otherwise = Nothing
essEq' _ _ _ = Nothing

sidesTrue :: Rule -> [Sentence] -> Bool
sidesTrue (Rule _ _ side _) ant = sidesTrue' side ant
sidesTrue (RuleP _ _ side _) ant = sidesTrue' side ant
sidesTrue' :: [SideCon] -> [Sentence] -> Bool
sidesTrue' (x:xs) ant 
	| x ant = sidesTrue' xs ant
	| otherwise = False
sidesTrue' [] _ = True

apRle :: Rule -> [Sentence] -> Sentence -> Maybe TInfo
apRle rle ant s
	| sidesTrue rle (s:ant) = apRle' rle ant
	| otherwise = Nothing
apRle' :: Rule -> [Sentence] -> Maybe TInfo 
apRle' (Rule str l sid con) ant
	| s == Nothing = Nothing
	| otherwise = Just(TInfo [] (convertArb s con))
	where s = essEqOp l ant (Just [])
apRle' (RuleP str l sid con) ant
	| s == Nothing = Nothing
	| otherwise = Just(TInfo (map (convertAnt s) l) (convertArb s con))
	where s = essEqOp (map getRef l) ant (Just [])

convertAnt :: Maybe [AsgnArb] -> PreSent -> PreSent
convertAnt asn (PS a l) = PS (convertArb asn a) (map (convertArb asn) l)
-- End Rule Application

preAm = "\\documentclass{article}\n\\usepackage{bussproofs} \n\\begin{document}" 
post = "\n\\end{document}"

toBuss :: Proof -> FilePath -> IO()
toBuss (Proof a c f) s 
	| conSolved (Proof a c f) = writeFile (s ++ ".tex") ((preAm ++ (toLatex (rmvMaybe (getProof (Proof a c f))))) ++ post) 
	| otherwise = writeFile (s ++ ".tex") ((preAm ++ (concat(map toLatex f))) ++ post) 

dotAry = ["Un","Bin","Trin","Quatern","Quin"] 

toLatex :: PT Sentence -> String
toLatex p = "\n\\begin{prooftree}" ++ (toLatex' p) ++ "\n\\end{prooftree}"
toLatex' :: PT Sentence -> String 
toLatex' p 
	| l > 5 = "BussProof cannot handle more than 5 PreSent"
	| l == 0 = "\n\\AxiomC{" ++ (show (root p)) ++ "}" 
	| otherwise = (concat (map toLatex' (chd p))) ++ "\n\\LeftLabel{"++ (show (getRule p)) ++"}\n\\" ++ (dotAry!!(l - 1)) ++ "aryInfC{" ++ (show (root p)) ++ "}" 
	where l = length(chd p)











