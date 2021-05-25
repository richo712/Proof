module Type () where 
import Data.List
import Test

data Assign = Assign Char String
	deriving(Show,Eq)
	
ts :: Sentence -> Sentence -> Sentence
ts a b = Op2 "typ" a b
	
type Context = [Assign]

a = Arb 'A'
b = Arb 'B'
c = Arb 'C'

delta :: Context
delta = [
	 (Assign 'a' "Str")
	,(Assign 'b' "Str")
	,(Assign 'x' "Int")
	,(Assign 'y' "Int")
	]
vars = ['a' ..  'z']
typs = ["Int","Bool","Str"]

addS :: Sentence -> Sentence -> Sentence
addI :: Sentence -> Sentence -> Sentence
eq :: Sentence -> Sentence -> Sentence
toStr :: Sentence -> Sentence
addS a b = ts (Op2 "+" a b ) (vals 1 2)
addI a b = ts (Op2 "+" a b ) (vals 1 0)
eq a b = ts (Op2 "==" a b ) (vals 1 1)
toStr a = ts (Op1 "toStr" a) (vals 1 2)

getR :: Proof -> Pass -> Sentence
getR p s = a
	where (Op2 "typ" a b) = root (getTree p s)

isTS :: SideCon
isTS' :: Sentence -> Bool
isTS' (Op2 "typ" _ (Vld (Value x _))) = x == 1 
isTS' _ = False 
isTS l = and (map isTS' l) 

isVar :: SideCon
isVar ((Op2 "typ" x y):[])
	| s /= Nothing && t/=Nothing = (Assign (rmvMaybe s) (rmvMaybe t)) `elem` delta
	where 
	s = getVldData x vars
	t = getVldData y typs
isVarInt _ = False

rdm0 = crtPrf [] (eq (Op1 "toStr" (Op2 "+" (vals 0 23) (vals 0 24))) ((Op2 "+" (vals 0 0)) (vals 0 1)))
rdm1 = add2PrfS rdm0 varR [] (ts (vals 0 0) (vals 1 2)) 
rdm2 = add2PrfS rdm1 varR [] (ts (vals 0 1) (vals 1 2)) 
rdm3 = add2PrfS rdm2 varR [] (ts (vals 0 23) (vals 1 0)) 
rdm4 = add2PrfS rdm3 varR [] (ts (vals 0 24) (vals 1 0))
rdm5 = add2Prf  rdm4 addIntR [(Ref 2),(Ref 3)] (addI (vals 0 23) (vals 0 24)) 
rdm6 = add2Prf 	rdm5 toStrR [(Ref 4)] (toStr (getR rdm5 (Ref 4)))
rdm7 = add2Prf  rdm6 addStrR [(Ref 0),(Ref 1)] (addS (vals 0 0) (vals 0 1))
rdmf = add2Prf  rdm7 eqR [(Ref 5) , (Ref 6)] (eq (getR rdm7 (Ref 5)) (getR rdm7 (Ref 6)))

varR = (Rule "var" [] [isVar] (ts (Arb 'A') (Arb 'B')))
addIntR = (Rule "addInt" [(ts (Arb 'A') (Vld (Value 1 0))),(ts (Arb 'C') (Vld (Value 1 0)))] [] (ts (Op2 "+" (Arb 'A') (Arb 'C')) (Vld (Value 1 0))))
addStrR = (Rule "addStr" [(ts (Arb 'A') (Vld (Value 1 2))),(ts (Arb 'C') (Vld (Value 1 2)))] [] (ts (Op2 "+" (Arb 'A') (Arb 'C')) (Vld (Value 1 2))))
multIntR = (Rule "multInt" [(ts (Arb 'A') (Vld (Value 1 0))),(ts (Arb 'C') (Vld (Value 1 0)))] [] (ts (Op2 "*" (Arb 'A') (Arb 'C')) (Vld (Value 1 0))))
divIntR = (Rule "divInt" [(ts (Arb 'A') (Vld (Value 1 0))),(ts (Arb 'C') (Vld (Value 1 0)))] [] (ts (Op2 "/" (Arb 'A') (Arb 'C')) (Vld (Value 1 0))))
subIntR = (Rule "subInt" [(ts (Arb 'A') (Vld (Value 1 0))),(ts (Arb 'C') (Vld (Value 1 0)))] [] (ts (Op2 "-" (Arb 'A') (Arb 'C')) (Vld (Value 1 0))))
toStrR = (Rule "toStr" [(ts (Arb 'A') (Arb 'C'))] [isTS] (toStr (Arb 'A')))

eqR = (Rule "eq" [(ts a c),(ts b c)] [isTS] (eq a b))
neqR = (Rule "neq" [(ts a c),(ts b c)] [isTS] (ts (Op2 "/=" a b) (Vld (Value 1 1)))) 
orR = (Rule "or" [(ts a (vals 1 1)),(ts b (vals 1 1))] [] (ts (Op2 "or" a b) (Vld (Value 1 1)))) 
andR = (Rule "and" [(ts a (vals 1 1)),(ts b (vals 1 1))] [] (ts (Op2 "and" a b) (Vld (Value 1 1)))) 
 