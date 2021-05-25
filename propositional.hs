module Propositional () where 

import Data.List
import Test

a = Arb 'A'
b = Arb 'B' --Three Arb used in testing as a shorthand
c = Arb 'C'

tf = [True,False]

com0 = crtPrf [(Op2 "And" (a) (b))] (Op2 "And" (b) (a))
com1 = add2PrfS com0 andElmL [(Op2 "And" a b)] a
com2 = add2PrfS com1 andElmR [(Op2 "And" a b)] b
com3 = add2PrfS com2 andInt [b,a] (Op2 "And" b a)
com4 = spread a com3
com5 = spread b com4

tra0 = crtPrf [(Op2 "And" a b), (Op2 "And" b c)] (Op2 "And" a c)
tra1 = add2Prf tra0 andElmL [(Ant 0)] a
tra2 = add2Prf tra1 andElmR [(Ant 1)] c
tra3 = add2Prf tra2 andInt [(Ref 0),(Ref 1)] (Op2 "And" a c)

como0 = crtPrf [(Op2 "Or" a b)] (Op2 "Or" b a)
como1 = add2PrfS como0 orElm [(Op2 "Imp" (a) (Op2 "Or" b a)),(Op2 "Imp" (b) (Op2 "Or" b a)),(Op2 "Or" a b)] (Op2 "Or" b a)
como2 = add2PrfS como1 impInt [(Op2 "Or" b a)] (Op2 "Imp" a (Op2 "Or" b a))
como3 = add2PrfS como2 orIntt [a] (Op2 "Or" b a)
como4 = spread (Op2 "Or" b a) como3
como5 = add2PrfS como4 impInt [(Op2 "Or" b a)] (Op2 "Imp" b (Op2 "Or" b a))
como6 = add2PrfS como5 orInto [b] (Op2 "Or" b a)
como7 = cnnct como6 (Ref 3) (Ref 4)
como8 = spread (Op2 "Imp" a (Op2 "Or" b a)) como7
como9 = spread (Op2 "Imp" b (Op2 "Or" b a)) como8




xmid0 = crtPrf [] (Op2 "Or" b (Op1 "neg" b))
xmid1 = add2PrfS xmid0 raa [(Vld (Value 0 1))] (Op2 "Or" b (Op1 "neg" b))
xmid3 = cnnct 	 xmid2 (Ref 0) (Ref 1)
con0 = crtPrf [a,(Op1 "neg" a)] (Vld (Value 0 1))
con1 = add2Prf con0 negElm [(Ant 1)] (Op2 "Imp" a (Vld (Value 0 1)))
con2 = add2Prf con1 impElm [(Ant 0),(Ref 0)] (Vld (Value 0 1)) 
contra = makeNewRule "contra" [] con2
xmid2 = add2PrfS xmid1 contra [(Op2 "Or" b (Op1 "neg" b)),(Op1 "neg" (Op2 "Or" b (Op1 "neg" b)))] (Vld (Value 0 1))
xmid4 = add2PrfS xmid3 orInto [b] (Op2 "Or" b (Op1 "neg" b))
xmid5 = add2PrfS xmid4 raa [(Vld (Value 0 1))] b
xmid6 = add2PrfS xmid5 orIntt [(Op1 "neg" b)] (Op2 "Or" b (Op1 "neg" b)) 
xmid7 = cnnct 	 xmid6 (Ref 0) (Ref 2)
xmid8 = cnnct 	 xmid7 (Ref 0) (Ref 3)
xmid9 = cnnct 	 xmid8 (Ref 0) (Ref 1)
xmid10= cnnct 	 xmid9 (Ref 0) (Ref 4)

xmid = makeNewRule "xmid" [] xmid5
commute = makeNewRule "commute" [] com5
trans = makeNewRule "trans" [] tra3

andInt = (Rule "andInt" [a,b] [] (Op2 "And" a b))  
andElmL = (Rule "andElmL" [(Op2 "And" a b)] [] a)
andElmR = (Rule "andElmR" [(Op2 "And" a b)] [] b)
orElm = (Rule "orElm" [(Op2 "Imp" (a) (b)),(Op2 "Imp" (c) (b)),(Op2 "Or" (a) (c))] [] (b))
orInto = (Rule "orInto" [a] [] (Op2 "Or" a b))
orIntt = (Rule "orIntt" [b] [] (Op2 "Or" a b))
impInt = (RuleP "impInt" [(PS a [b])] [] (Op2 "Imp" b a))
impElm = (Rule "impElm" [a,(Op2 "Imp" a b)] [] b)
raa = (RuleP "raa" [(PS (Vld (Value 0 1)) [(Op1 "neg" a)])] [] a )
negElm = (Rule "negElm" [(Op1 "neg" a)] [] (Op2 "Imp" a (Vld (Value 0 1))))
unit = (Rule "unit" [] [] (Vld(Value 0 0)))