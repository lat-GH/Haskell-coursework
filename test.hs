test :: Type -> Bool
test (At a) = True

test2 :: Atom -> Bool
test2 a = True

makeList1 :: Type -> [Atom]
makeList1 (At t) = [t]
makeList1 (At t :-> s) = t: makeList s

concat :: [Int] -> [Int] -> [Int]
conact a b = a : b


--FAILED ATTEMPT in making the substitution a variable in step 
step :: State -> State
--turn the Upair into a sub and add it to the front of State
--apply the substitution to the elements of the [Upair] and add as the second half of the State
let P_sub = (getAtom(snd p), fst p)
in step (u, p:px) = ((u ++ [P_sub]) , sub_u P_sub px)--case b

--REVERSE VERSION 
step :: State -> State 
step (u, (At a , At b) : px)
  | a == b = (u, px)--case a
  | otherwise = (u ++ [(a , At b)], px)
step (u, ((At a) , (t :-> s)) :px) --case b.1
  | occurs a (t :-> s) = error "FAIL" --("atom ",a," occurs in ", (t :-> s))
  | otherwise = ((u ++ [(a, (t :-> s))]) , sub_u (a, (t :-> s)) px ) 
step (u, ((t :-> s), (At a)) :px) -- case b.2
  | occurs a (t :-> s) = error "FAIL"
  | otherwise = ((u ++ [(a, (t :-> s))]) , sub_u (a, (t :-> s)) px ) 
step (u, (( t :-> s), ( r :-> v)) :px) = (u, case_c (( t :-> s), ( r :-> v)) ++ px) --case c


--FAILED unify
----unify [] = []
----unify (p:px) = fst (step ((unify px), p:px))
--unify (p:px) = unify(snd (step([], p:px)))
--unify (p:px) = step([], p:px)


----ATTEMPT 1 AT derive0
derive0 :: Term -> Derivation
derive0 (Variable v) = Axiom (c,v,At "")
derive0 (Lambda v t) = aux (c, v t, At "")
derive0 (Apply t r) = Application (c, t r ,At "") (c,(derive0 t),At "") (c,(derive0 r),At "")
  where
    aux :: Judgement -> Derivation
    aux (c, (Lambda v t), y) = Abstraction (c,v t ,y) (c++[(v, At "")], t ,At "")


--ATTEMOT 2 at deriv0
derive0 :: Term -> Derivation
derive0 (Variable v) = Axiom ([(v,At "" )], Variable v,At "")
derive0 (Apply t r) = Application (freeToContext (free (Apply t r)), (Apply t r) ,At "") (freeToContext (free (Apply t r)),(derive0 t),At "") (freeToContext (free (Apply t r)),(derive0 r),At "") -- dont need to alter the context
derive0 (Lambda v t) = abstractContext (freeToContext (free (v t)), v t, At "")
  where
    abstractContext :: Judgement -> Derivation
    abstractContext (c, (Lambda v t), y) = Abstraction (c,v t ,y) (c++[(v, At "")], t ,At "")

--attempting to use minus for checking if a var occurs in a context
minus :: Ord a => [a] -> [a] -> [a]
minus [(Variable x, At "a"),(Variable y, At "b")] [(Variable x, At "a")]


--WORING VERIONS of derive0 -- without checking if the context already contains the variable your adding
derive0 :: Term -> Derivation
derive0 (Variable v) = Axiom ([(v,At "" )], Variable v,At "")
derive0 (Apply t r) = Application (freeToContext (free (Apply t r)), (Apply t r) ,At "") (derive0 t) (derive0 r)-- dont need to alter the context
derive0 (Lambda v t) = abstractContext (freeToContext (free (Lambda v t)), (Lambda v t), At "")
  where
    abstractContext :: Judgement -> Derivation
    abstractContext (c, (Variable v), y) = Axiom (c, (Variable v), y) 
    abstractContext (c, (Apply t e), y) = Application (c, (Apply t e), y) (abstractContext (c, t, y)) (abstractContext (c, e, y))
    abstractContext (c, (Lambda v t), y) = Abstraction (c,(Lambda v t) ,y) (abstractContext (c++[(v, At "")], t ,At ""))

--WORKING VERSION OF derive0 -- where does check if the variable your adding is already in the context
derive0 :: Term -> Derivation
derive0 (Variable v) = Axiom ([(v,At "" )], Variable v,At "")
derive0 (Apply t r) = Application (freeToContext (free (Apply t r)), (Apply t r) ,At "") (derive0 t) (derive0 r)-- dont need to alter the context
derive0 (Lambda v t) = abstractContext (freeToContext (free (Lambda v t)), (Lambda v t), At "")
  where
    abstractContext :: Judgement -> Derivation
    abstractContext (c, (Variable v), y) = Axiom (c, (Variable v), y) 
    abstractContext (c, (Apply t e), y) = Application (c, (Apply t e), y) (abstractContext (c, t, y)) (abstractContext (c, e, y))
    abstractContext (c, (Lambda v t), y) 
      | occursInContext v c == True = Abstraction ((removeFromContext v c),(Lambda v t) ,y) (abstractContext ((removeFromContext v c)++[(v, At "")], t ,At ""))
      | otherwise = Abstraction (c,(Lambda v t) ,y) (abstractContext (c++[(v, At "")], t ,At ""))

--IF cant get this to work try elem
occursInContext :: Var -> Context -> Bool
occursInContext v [] = False
occursInContext v ((a,t):cx) = v == a || occursInContext v cx

removeFromContext :: Var -> Context -> Context
removeFromContext v [] = []
removeFromContext v ((a,t):cx)
  |v == a = removeFromContext v cx
  | otherwise = (a,t) : removeFromContext v cx


--the orginal apptern matches when first tried to add abstract context
--derive0 (Variable v) = abstractContext ([(v,At "" )], Variable v,At "")
--derive0 (Apply t r) = abstractContext (freeToContext (free (Apply t r)), (Apply t r) ,At "") 
--derive0 (Lambda v t) = abstractContext (freeToContext (free (Lambda v t)), (Lambda v t), At "")


--WORKING VERSION OF GET EVEN Atoms
filterIndexed :: (a -> Int -> Bool) -> [a] -> [a]
filterIndexed p xs = [x|(x,i) <- zip xs [0..], p x i]

evenAtom :: Atom -> Int -> Bool
evenAtom a i = (mod i 2) == 0

getEvenAtoms :: [Atom] -> [Atom]
getEvenAtoms = filterIndexed evenAtom

list2 :: [Atom]
list2 = getEvenAtoms atoms2


--FAILED ATTTEMPT AT GENRALISEING SO IT ISNT JUST EVEN INDEXX
filterIndexed :: (a -> Int -> Int -> Bool) -> [a] -> [a]
filterIndexed p xs = [x|(x,i) <- zip xs [0..], p x n i]

anyAtom :: Atom -> Int -> Int -> Bool
anyAtom a n i = (mod i n) == 0

getEvenAtoms :: [Atom] -> Int -> [Atom]
getEvenAtoms a n = filterIndexed anyAtom a n

list2 :: [Atom]
list2 = getEvenAtoms atoms2 3


--trail of upairs semi working 
upairs (Axiom (c,(Variable v), y )) = [(y, (find v c))]
upairs (Abstraction (c, (Lambda v t), y) e) = [(y,y)] ++ upairs e
upairs (Application (c, (Apply t r), y) e m) = [(y,y)] ++ upairs e ++ upairs m

--types dont complain for this one
upairs (Axiom (c,(Variable v), y )) = [(y, (find v c))]
upairs (Abstraction (c, (Lambda v t), y) e) = [(y, ((find v c) :-> y))] ++ upairs e
upairs (Application (c, (Apply t r), y) e m) = [(y, (y :-> y))] ++ upairs e  ++ upairs m 

--WORKING upairs WITHOUT let
upairs :: Derivation -> [Upair]
upairs (Axiom (c,(Variable v), y )) = [(y, (find v c))]
upairs (Abstraction (c, (Lambda v t), y) e) = [(y, ((find v (getCnxtJdg ((nextLevelDev (Abstraction (c, (Lambda v t), y) e) 1) !! 0))) :-> getTypeJdg ((nextLevelDev (Abstraction (c, (Lambda v t), y) e) 1) !! 0)))] ++ upairs e
upairs (Application (c, (Apply t r), y) e m) = [(getTypeJdg ((nextLevelDev ((Application (c, (Apply t r), y) e m)) 1) !! 0), ((getTypeJdg ((nextLevelDev ((Application (c, (Apply t r), y) e m)) 1) !! 1)) :-> y))] ++ upairs e  ++ upairs m 


------------------------------------------working out whats working---------------------------------------
type Sub = (Atom,Type)
type Upair = (Type,Type)
type State = ([Sub],[Upair])

--Sub ("remove", keep)
--Upair (remove, keep)
-- State = (working result, set of Upairs)


([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("f",b)], [(c,b -> a),(c,g -> i),(i,g)])
([("f",b),("i",g)], [(c,b -> a),(c,g -> g)])
([("f",b),("i",g)], [(c,b -> a),(c,g)])
([("f",b),("i",g),("c",g)], [(c,b -> a)])
([("f",b),("i",g),("c",g),("c",b -> a)],[]])-OR- ([("f",b),("i",g),("c",b -> a)],[]])



ALTERNATILEY IF WORKED WITH IT AS
--Sub ("keep", remove)  WRONG because we want to replace all of the Atoms with Types??
--Upair (remove, keep)
-- State = (working result, set of Upairs)
([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("b",f)], [(c,b -> a),(c,g -> i),(i,g)])
([("b",f),("g",i)], [(c,b -> a),(c,g -> g)])
([("b",f),("g",i)], [(c,b -> a),(c,g)])
([("b",f),("g",i),("c",g)], [(c,b -> a)])--([("b",f),("c",i),("c",g)], [(c,b -> a)])
([("b",f),("g",i),("c",g),("b->a", c)], [])     --([("b",f),("b -> a",i),("b -> a",g)], [])


ALTERNATILEY IF WORKED WITH IT AS
--Sub ("remove", keep)
--Upair (keep, remove)
-- State = (working result, set of Upairs)

--whiteboard example

[[],[(d, a->e),(e, b->n),(n, c->t),(a, c->l),(b, c->k),(l, k->t)]]
[[("d", a->e)],[(e, b->n),(n, c->t),(a, c->l),(b, c->k),(l, k->t)]]
[[("d", a->e),(e, b->n)],[(n, c->t),(a, c->l),(b, c->k),(l, k->t)]]
[[("d", a->b->n),("e", b->n)],[(n, c->t),(a, c->l),(b, c->k),(l, k->t)]] --repaced the value for e
[[("d", a->b->n),("e", b->n),("n", c->t)],[(a, c->l),(b, c->k),(l, k->t)]]
[[("d", a->b->c->t),("e", b->c->t),("n", c->t)],[(a, c->l),(b, c->k),(l, k->t)]]
[[("d", a->b->c->t),("e", b->c->t),("n", c->t),("l", k->t)],[(a, c->l),(b, c->k)]] --taking the upair at the end of the list because willem wanted???
[[("d", a->b->c->t),("e", b->c->t),("n", c->t),("l", k->t)],[(a, c->k->t),(b, c->k)]]--then had to change the values for l in the upairs instead of in the sub
[[("d", a->b->c->t),("e", b->c->t),("n", c->t),("l", k->t),("a", c->k->t)],[(b, c->k)]]
[[("d", (c->k->t)->b->c->t),("e", b->c->t),("n", c->t),("l", k->t),("a", c->k->t)],[(b, c->k)]]
[[("d", (c->k->t)->b->c->t),("e", b->c->t),("n", c->t),("l", k->t),("a", c->k->t),("b", c->k)],[]]
[[("d", (c->k->t)->( c->k)->c->t),("e", (c->k)->c->t),("n", c->t),("l", k->t),("a", c->k->t),("b", c->k)],[]]


newest logic willem logic, applied to the upairs of n1

([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("f",b)], [(c,f -> a),(c,g -> i),(i,g)])
([("f",b)], [(c,b -> a),(c,g -> i),(i,g)])
([("f",b),("i",g)], [(c,b -> a),(c,g -> i)])
([("f",b),("i",g)], [(c,b -> a),(c,g -> g)])
([("f",b),("i",g)], [(c,b -> a),(c,g)])
([("f",b),("i",g),("c",g)], [(c,b -> a)])
([("f",b),("i",g),("c",g)], [(g,b -> a)])
([("f",b),("i",g),("c",g),("g",b -> a)], [])
([("f",b),("i",b -> a),("c",b -> a),("g",b -> a)], [])

([("f",At "b"),("i",At "b" :-> At "a"),("c",At "b" :-> At "a"),("g",At "b" :-> At "a")], []) -- will substitute this as told, so no error with the substitution method


are the upiars right -- YES THEY ARE
[(c,d->a),(c,f->h),(h,f),(d,b)]
[(c,f->a),(c,g->i),(i,g),(f,b)]

[(c,d->a),(c,f->h),(h,f),(d,b)]


--------------LHS to RHS 

([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f -> a,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f,a),(g,i),(i,g),(f,b)]) -- c. CASE
([("c",f -> a),("f",a)], [(g,i),(i,g),(f,b)])
([("c",a -> a),("f",a)], [(g,i),(i,g),(f,b)])
([("c",a),("f",a)], [(g,i),(i,g),(f,b)])
([("c",a),("f",a),("g",i)], [(i,g),(f,b)])
([("c",a),("f",a),("g",i)], [(i,i),(f,b)])
([("c",a),("f",a),("g",i)], [(f,b)])
([("c",a),("f",a),("g",i),("f",b)], [])
([("c",a),("b",a),("g",i),("f",b)], [])

([("c",At "a"),("b",At "a"),("g", At "i"),("f",At "b")], [])


--------LHS to RHS -----attempt 2!!!
([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f -> a,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f,i),(g,a),(i,g),(f,b)]) -- c. CASE WONR AGAIN
([("c",f -> a),("f",i)], [(g,a),(i,g),(f,b)])
([("c",i -> a),("f",i)], [(g,a),(i,g),(f,b)])
([("c",i -> a),("f",i),("g",a)], [(i,g),(f,b)])
([("c",i -> a),("f",i),("g",a)], [(i,a),(f,b)])
([("c",a -> a),("f",a),("g",a),("i",a)], [(f,b)])
([("c",a),("f",a),("g",a),("i",a)], [(f,b)])
([("c",a),("f",a),("g",a),("i",a),("f",b)], [])
([("c",a),("b",a),("g",a),("i",a),("f",b)], [])

([("c",At "a"),("b",At "a"),("g",At "a"),("i",At "a"),("f",At "b")], [])


--ORIGINAL WORKING step
--takes the list Upairs and converts them into a list substrituitons based on the 3 cases a,b,c
step :: State -> State 
step (u, (At a , At b) : px) -- case a
  | a == b = (u, px)--case a
  | otherwise = ([(a , At b)] ++ u, px)
step (u, ((At a) , (t :-> s)) :px) --case b.1
  | occurs a (t :-> s) = error "FAIL" --("atom ",a," occurs in ", (t :-> s))
  | otherwise = (([(a, (t :-> s))] ++ u) , sub_u (a, (t :-> s)) px ) 
step (u, ((t :-> s), (At a)) :px) -- case b.2
  | occurs a (t :-> s) = error "FAIL"
  | otherwise = (([(a, (t :-> s))] ++ u) , sub_u (a, (t :-> s)) px ) 
step (u, (( t :-> s), ( r :-> v)) :px) = (u, case_c (( t :-> s), ( r :-> v)) ++ px) --case c


([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f -> a,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f,g),(a,i),(i,g),(f,b)]) -- c Case
([("c",f -> a),("f",g)], [(a,i),(i,g),(f,b)]) --updates the upairs as well as the substitutiosn
([("c",g -> a),("f",g)], [(a,i),(i,g),(g,b)])
([("c",g -> a),("f",g),("a",i)], [(i,g),(g,b)])
([("c",g -> i),("f",g),("a",i)], [(i,g),(g,b)])
([("c",g -> i),("f",g),("a",i),("i",g)], [(g,b)])
([("c",g -> g),("f",g),("a",g),("i",g)], [(g,b)])
([("c",g -> g),("f",g),("a",g),("i",g),("g",b)], [])
([("c",b -> b),("f",b),("a",b),("i",b),("g",b)], [])



-- working out why the unify [u3, u4] is WRONG attempting a new C.case
([("a",c -> d),("b",e)],[((c -> d) -> e,(c -> d) -> c -> c)])
([("a",c -> d),("b",e)],[(((c -> d),(c -> d) -> c), (c,e)])
([("a",c -> d),("b",e)],[(c,c->d),(d,c),(c,e)]) 
([("a",c -> d),("b",e),("c",c->d)],[(d,c),(c,e)]) 
([("a",(c->d) -> d),("b",e),("c",c->d)],[(d,(c->d)),((c->d),e)]) 



--case C before used the sub_s
([], [(c,f -> a),(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(c,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f -> a,g -> i),(i,g),(f,b)])
([("c",f -> a)], [(f,g),(a,i),(i,g),(f,b)])
([("c",f -> a),("f",g)], [(a,i),(i,g),(f,b)])
([("c",f -> a),("f",g)], [(a,i),(i,g),(g,b)])
([("c",f -> a),("f",g),("a",i)], [(i,g),(g,b)])
([("c",f -> a),("f",g),("a",i),("i",g)], [(g,b)])
([("c",f -> a),("f",g),("a",i),("i",g),("g",b)], [])
