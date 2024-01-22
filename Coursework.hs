
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions
--like a dictionary serach looks for the key and will return value IF finds it
find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs

--merges two lists together
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

--keeps an item fronm the firt list if its less than the item from the second list
--gets rid of both items if they are equal
--get rid of item from second list is its less than the item from the first list
--only keeps itesm from the first list is they are less than the items in seconf list???
minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

--returns a list of free variables from a term
free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

--Atoms are the placeholders for the Types
type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
-- list a to z and another list a cons i for a from a-z and i from 1 to infinty
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"

t4 :: Type
t4 = At "e" :-> (At "f" :-> At "d")




------------------------- Assignment 1
--checks if an Atom appears in a type
occurs :: Atom -> Type -> Bool
occurs a (At t) = a == t || False 
occurs a (t :-> s) = occurs a t || occurs a s

--finds all of the Atoms in a type
findAtoms :: Type -> [Atom]
findAtoms (t :-> s) = sortList(makeList (t) ++ makeList(s))

--turns the type into a list of its atoms
makeList :: Type -> [Atom]
makeList (At t) = [t]
makeList(t :-> s) = makeList t ++  makeList s

--sorts a list of atoms
sortList :: [Atom] -> [Atom]
sortList []  = []
sortList [x] = [x]
sortList xs  = merge (sortList (take n xs)) (sortList (drop n xs))
  where
    n = div (length xs) 2

------------------------- Type substitution

type Sub = (Atom,Type)
-- ^^ replace Atom with Type
--Sub ("remove", keep)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

-- performs a substituation on a type and returns the orignal type with all its new substitutions
sub :: Sub -> Type -> Type
sub u (t :-> s) = sub u t :-> sub u s
sub u (At t)
  | fst u == t  = snd u
  | otherwise  = At t

--perfomrs a list of differnt substitutions on a type
subs :: [Sub] -> Type -> Type
subs [] (At a) = At a
subs [] (t :-> s) = (t :-> s)
subs (u:ux) (At a) = sub u (subs ux (At a))
subs (u:ux) (t :-> s) = sub u (subs ux (t :-> s))

------------------------- Unification
type Upair = (Type,Type)
type State = ([Sub],[Upair])
-- State = (working result, set of Upairs)

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

--performs a substitution on a list of unipairs
--where find snd of Sub replaces with fst of Sub
sub_u :: Sub -> [Upair] -> [Upair]
sub_u _ [] = []
sub_u u (p:px) = [(sub u (fst p), sub u (snd p))] ++ sub_u u px

--Handles the case c of converting an pair of arrow type into singulars Upairs
case_c :: Upair -> [Upair]
case_c (t :-> s, r :-> v) = [(t,r),(s,v)]

{-
--takes the list Upairs and converts them into a list substrituitons based on the 3 cases a,b,c
step :: State -> State 
step (u, (At a , At b) : px) -- case a
  | a == b = (u, px)--case a
  | otherwise = ((sub_s (a , At b) u) ++ [(a , At b)], (sub_u (a , At b) px))
step (u, ((At a) , (t :-> s)) :px) --case b.1
  | occurs a (t :-> s) = error "FAIL" --("atom ",a," occurs in ", (t :-> s))
  | otherwise = (((sub_s (a, (t :-> s)) u) ++ [(a, (t :-> s))]) , sub_u (a, (t :-> s)) px ) 
step (u, ((t :-> s), (At a)) :px) -- case b.2
  | occurs a (t :-> s) = error "FAIL"
  | otherwise = (((sub_s (a, (t :-> s)) u) ++ [(a, (t :-> s))]) , sub_u (a, (t :-> s)) px ) 
step (u, (( t :-> s), ( r :-> v)) :px) = (u, case_c (( t :-> s), ( r :-> v)) ++ px) --case c --DO YOU NEED TO APPLY SUBSTITUTION TO THE px
-}

--takes the list Upairs and converts them into a list substrituitons based on the 3 cases a,b,c
step :: State -> State 
step (u, (At a , At b) : px) -- case a
  | a == b = (u, px)--case a
  | otherwise = ([(a , At b)] ++ u, (sub_u (a , At b) px))
step (u, ((At a) , (t :-> s)) :px) --case b.1
  | occurs a (t :-> s) = error "FAIL" --("atom ",a," occurs in ", (t :-> s))
  | otherwise = (([(a, (t :-> s))] ++ u) , sub_u (a, (t :-> s)) px ) 
step (u, ((t :-> s), (At a)) :px) -- case b.2
  | occurs a (t :-> s) = error "FAIL"
  | otherwise = (([(a, (t :-> s))] ++ u) , sub_u (a, (t :-> s)) px ) 
step (u, (( t :-> s), ( r :-> v)) :px) = (u, case_c (( t :-> s), ( r :-> v)) ++ px) --case c

--implents all of the steps till there are no more unifcations pairs
stepAll :: State -> State
stepAll(u, []) = (u, [])
stepAll (u,p) = stepAll (step (u,p))

--runs step all given a list of Upairs and returns the final substitution
unify :: [Upair] -> [Sub] 
unify p = fst( stepAll([],p) )

------------------------- Assignment 4
type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = 
   Axiom  Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")
n2 = Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z"))

d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )
     

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )

--will be the first full element of the derivation - gets the one at the bottom of the tree
conclusion :: Derivation -> Judgement
conclusion(Axiom j) = j
conclusion (Abstraction j d) = j
conclusion (Application j d e) = j

--applies a substrituiton to a context
subs_ctx :: [Sub] -> Context -> Context
subs_ctx s [] = []
subs_ctx s (c:cx) = [(fst c, (subs s (snd c)))] ++ (subs_ctx s cx)

--applies a substituation to a Judgement
subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (c, r, y) = ((subs_ctx s c), r, (subs s y))

--applies a substituation to a derivation
subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Axiom a) = Axiom (subs_jdg s a)
subs_der s (Abstraction b d) = Abstraction (subs_jdg s b) (subs_der s d)
subs_der s (Application p d e) = Application (subs_jdg s p) (subs_der s d) (subs_der s e)


------------------------- Typesetting derivations

--used to display a derivation tree all pretty

instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5

--adds the list of variables to a context
freeToContext :: [Var] -> Context
freeToContext [] = []
freeToContext (v:vs) = [(v, At "")] ++ freeToContext vs

--checks if a var occurs in a context
occursInContext :: Var -> Context -> Bool
occursInContext v [] = False
occursInContext v ((a,t):cx) = v == a || occursInContext v cx

--removes a (Var,Type) from a context
removeFromContext :: Var -> Context -> Context
removeFromContext v [] = []
removeFromContext v ((a,t):cx)
  |v == a = removeFromContext v cx
  | otherwise = (a,t) : removeFromContext v cx

--populates an empty derivation tree 
derive0 :: Term -> Derivation
derive0 t = aux (freeToContext(free t), t,  At "")
  where
    aux :: Judgement -> Derivation
    aux (c, (Variable v), y) 
      |occursInContext v c == True = Axiom (c, (Variable v), At "") --need to make sure it doenst add values to the context unesscalriy
      |otherwise = Axiom (c ++ [(v,At "" )], (Variable v), At "")
    aux (c, (Apply t r), y) = Application (c, (Apply t r), y) (aux (c, t, At "")) (aux (c, r, At ""))
    aux (c, (Lambda v t), y) 
      | occursInContext v c == True = Abstraction ((removeFromContext v c),(Lambda v t) ,y) (aux ((removeFromContext v c)++[(v, At "")], t ,At ""))
      | otherwise = Abstraction (c,(Lambda v t) ,y) (aux (c++[(v, At "")], t ,At ""))

--made a shorter list of atoms to test with
atoms2 :: [Atom]
-- list a to z and another list a cons i for a from a-z and i from 1 to infinty
atoms2 = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..5], a <- ['a'..'z'] ]

-----all the mini functions created to split the stream of atoms into odds and evens---------
--ususe the function p to filter the based on the indexes of the list
filterIndexed :: (a -> Int -> Bool) -> [a] -> [a]
filterIndexed p xs = [x|(x,i) <- zip xs [0..], p x i]

--retunrs true if the int with the atom is even
evenAtom :: Atom -> Int -> Bool
--evenAtom a i = (mod i 2) == 0
evenAtom a i = even i

oddAtom :: Atom -> Int -> Bool
oddAtom a i = odd i

--creates a new list only containing the atoms at even indicies (NOT the even atoms)
getEvenAtoms :: [Atom] -> [Atom]
getEvenAtoms = filterIndexed evenAtom

getOddAtoms :: [Atom] -> [Atom]
getOddAtoms = filterIndexed oddAtom

--test lists
list1 :: [Atom]
list1 = drop 2 atoms2

list2 :: [Atom]
list2 = getEvenAtoms atoms2

list3 :: [Atom]
list3 = getOddAtoms atoms2

listodd :: [Atom]
listodd = getOddAtoms list1

listeven :: [Atom]
listeven = getEvenAtoms list1
------------------------------------------------------------------------------------------------


--adds the list of variables to a context
freeToContext2 :: [Atom] -> [Var] -> Context
freeToContext2 _ [] = []
freeToContext2 (a:as) (v:vs) = [(v, At a)] ++ freeToContext2 as vs


derive1 :: Term -> Derivation
derive1 t = aux (drop (length (free t) + 1) atoms2) (freeToContext2 (drop 1 atoms2) (free t), t,  At (atoms2 !! 0))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux a (c, (Variable v), y) --WHY DOES THE AXIOM CASE skip letter from the atom list it is give!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      |occursInContext v c == True = (Axiom (c, (Variable v), At ( a !! 0)))
      |otherwise = Axiom (c ++ [(v,At (a !! 1))], (Variable v), At (a !! 0))
    aux a (c, (Apply t r), y) = Application (c, (Apply t r), y) (aux (getEvenAtoms (drop 2 a)) (c, t, At (a !! 0))) (aux (getOddAtoms (drop 2 a)) (c, r, At (a !! 1)))
    aux a (c, (Lambda v t), y) 
      | occursInContext v c == True = Abstraction (c ,(Lambda v t) ,y) (aux (drop 2 a) ((removeFromContext v c)++[(v, At (a !! 1))], t ,At (a !! 0))) --the first context of the abtratsct used to be this: (removeFromContext v c) instead of c
      | otherwise = Abstraction (c,(Lambda v t) ,y) (aux (drop 2 a) (c++[(v, At (a !! 1))], t ,At (a !! 0)))

upairs :: Derivation -> [Upair]
upairs (Axiom (c,(Variable v), y )) = [(y, (find v c))]
upairs (Abstraction (c, (Lambda v t), y) e) = 
  let nxt = nextLevelDev (Abstraction (c, (Lambda v t), y) e) 1
  in  [(y, ((find v (getCnxtJdg ((nxt) !! 0))) :-> getTypeJdg ((nxt) !! 0)))] ++ upairs e
upairs (Application (c, (Apply t r), y) e m) = 
  let nxt = nextLevelDev ((Application (c, (Apply t r), y) e m)) 1
  in [(getTypeJdg ((nxt) !! 0), ((getTypeJdg ((nxt) !! 1)) :-> y))] ++ upairs e  ++ upairs m 

--gets the next judgemtns of a derivation
nextLevelDev :: Derivation -> Int -> [Judgement]
nextLevelDev (Axiom (c,(Variable v), y )) _ = [(c,(Variable v), y )]
nextLevelDev (Abstraction (c, (Lambda v t), y) e) n
  | n == 2 = [(c, (Lambda v t), y)]
  | otherwise = nextLevelDev e (n+1)
nextLevelDev (Application (c, (Apply t r), y) e m) n
  | n == 2 = [(c, (Apply t r), y)]
  | otherwise = (nextLevelDev e (n+1)) ++ (nextLevelDev m (n+1))

--get the type of a Judgement
getTypeJdg :: Judgement -> Type
getTypeJdg (c, t, y) = y

getCnxtJdg :: Judgement -> Context
getCnxtJdg (c, t, y) = c



derive :: Term -> Derivation
derive t = subs_der (unify (upairs (derive1 t))) (derive1 t)



------------------------------used for testing
deriveFINAL ::Term -> Judgement
deriveFINAL t = conclusion (subs_der (unify (upairs (derive1 t))) (derive1 t))

correctUpairs :: [Upair]
correctUpairs = [(At "c", At "f" :-> At "a"),(At "c",At "g" :-> At "i"),(At "i",At "g"),(At "f",At "b")]

testState1 :: State
testState1 = ([],correctUpairs)

testState2 :: State
testState2 = ([], [(At "c",At "h" :-> At "a"),(At "c", At "d" :-> At "e"),(At "f", At "g" :->At "e"),(At "f",At "d"),(At "g",At "b"),(At "h",At "i" :-> At "j"),(At "j",At "i")])

willSub :: [Sub]
willSub = [("f",At "b"),("i",At "b" :-> At "a"),("c",At "b" :-> At "a"),("g",At "b" :-> At "a")]

willSub2 :: [Sub]
willSub2 = [("c",At "a"),("b",At "a"),("g", At "i"),("f",At "b")]

willSub3 :: [Sub]
willSub3 = [("c",At "a"),("b",At "a"),("g",At "a"),("i",At "a"),("f",At "b")]

noSub_s :: [Sub]
noSub_s = [("c",At "f" :-> At "a"),("f",At "g"),("a",At "i"),("i",At "g"),("g",At "b")]
