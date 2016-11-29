
\begin{code}
{-# OPTIONS --no-termination-check  #-}

open import Container hiding (map)
open import Composition
open import Sum
open import Product
open import Exponential
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum 
open import Data.Empty
open import Function renaming (_∘_ to _∘ₛ_ ; id to idₛ)
open import Relation.Binary.HeterogeneousEquality renaming ([_] to [_]ᵢ)
\end{code}

%<*clist>
\begin{code}
cList : Cont
cList = ℕ ◃ Fin
\end{code}
%</clist>

%<*list>
\begin{code}
List : Set → Set
List = ⟦ cList ⟧
\end{code}
%</list>

%<*listconstructors>
\begin{code}
nil : ∀{X} → List X
nil = 0 , (λ ())

cons : ∀{X} → X → List X → List X
cons x (s , f) = suc s , (λ { zero → x ; (suc i) → f i })
\end{code}
%</listconstructors>


%<*cId>
\begin{code}
cId : Cont
cId = ⊤ ◃ (λ _ → ⊤ )
\end{code}
%</cId>
%<*Id>
\begin{code}
Id : Set → Set
Id = ⟦ cId ⟧

identity : ∀{X} → X → Id X
identity x = tt , (λ _ → x)
\end{code}
%</Id>

%<*cK>
\begin{code}
cK : Set → Cont
cK A = A ◃ (λ _ → ⊥)
\end{code}
%</cK>

%<*K>
\begin{code}
K : Set → Set → Set
K A = ⟦ cK A ⟧
\end{code}
%</K>
%<*dos>
\begin{code}
dos : K ℕ ⊥
dos = 2 , (λ { () })
\end{code}
%</dos>


%<*cMaybe>
\begin{code}
cMaybe : Cont
cMaybe = Bool ◃ (λ { false → ⊥ ; true → ⊤ }) 
\end{code}
%</cMaybe>

%<*maybe>
\begin{code}
Maybe : Set → Set
Maybe = ⟦ cMaybe ⟧

nothing : ∀{X} → Maybe X
nothing = false , (λ { () })

just : ∀{X} → X → Maybe X
just x = true , (λ { tt → x })
\end{code}
%</maybe>



%<*writer>
\begin{code}
cWriter : Set → Cont
cWriter W = W ◃ (λ w → ⊤)

Writer : Set → Set → Set
Writer W = ⟦ cWriter W ⟧ 

\end{code}
%</writer>


%<*cReader>
\begin{code}
cReader : Set → Cont
cReader E = ⊤ ◃ (λ {tt → E})
\end{code}
%</cReader>

%<*reader>
\begin{code}
Reader : Set → Set → Set
Reader E = ⟦ cReader E ⟧ 

reader : ∀{E X} → (E → X) → Reader E X
reader x = tt , x

\end{code}
%</reader>


runReader : ∀{E X} → Reader E X → E → X
runReader  (tt , f) x = f x

ask : ∀{E} → Reader E E
ask = tt , (λ z → z)

returnReader : ∀{E X} → X → Reader E X
returnReader x = tt , (λ _ → x)

>>=Reader : ∀{E X Y} → Reader E X → (X → Reader E Y) → Reader E Y
>>=Reader r f = tt , (λ x → runReader (f (runReader r x)) x)


%<*cState>
\begin{code}
cState : Set → Cont
cState S = (S → S) ◃ (λ x → S)
\end{code}
%</cState>

%<*state>
\begin{code}
State : Set → Set → Set
State S = ⟦ cState S ⟧ 

runState : ∀{S X} → State S X → S → X × S
runState (s , f) st = (f st) , (s st)

put : ∀{S} → S →  State S ⊤
put s = (λ x → s) , (λ _ → tt)

get : ∀{S} → State S S
get = (λ x → x) , (λ x → x)
\end{code}
%</state>

%<*cStream>
\begin{code}
cStream : Cont
cStream = ⊤ ◃ (λ {tt → ℕ})
\end{code}
%</cStream>


%<*Stream>
\begin{code}
Stream : Set → Set
Stream = ⟦ cStream ⟧

s : Stream ℕ
s = tt , (λ _ → 1)
\end{code}
%</Stream>

%<*treeSh>
\begin{code}
data TreeSh : Set where
  leafSh : TreeSh
  nodeSh : TreeSh → TreeSh → TreeSh
\end{code}
%</treeSh>


%<*treePos>
\begin{code}
data TreePos : TreeSh → Set where
  leafPos : TreePos leafSh
  nodePosL : ∀{l r} → TreePos l → TreePos (nodeSh l r)  
  nodePosR : ∀{l r} → TreePos r → TreePos (nodeSh l r)  
\end{code}
%</treePos>


%<*ctree>
\begin{code}
cTree : Cont
cTree = TreeSh ◃ TreePos
\end{code}
%</ctree>
x
%<*tree>
\begin{code}
Tree : Set → Set
Tree = ⟦ cTree ⟧

leaf : ∀{X} → X →  ⟦ cTree ⟧ X
leaf x = leafSh , (λ { leafPos → x })

node : ∀{X} → Tree X → Tree X → Tree X
node (sl , pl) (sr , pr) = nodeSh sl sr , (λ  { (nodePosL pos) → pl pos
                                              ; (nodePosR pos) → pr pos })
\end{code}
%</tree>


%<*chead>
\begin{code}
chead : cList ⇒ cMaybe
chead = (λ { 0 → false; (suc _) → true }),(λ { {0} (); {suc _} tt → zero})
\end{code}
%</chead>

%<*head>
\begin{code}
head : ∀{X} → List X → Maybe X
head = ⟦ chead ⟧ₘ 
\end{code}
%</head>

%<*creverse>
\begin{code}
inj : {n : ℕ} {i : Fin (suc n)} → Fin (suc n ∸ toℕ i) → Fin (suc n)
inj {i = zero} s = s
inj {zero} {suc ()} s
inj {suc n} {suc i} s = inject₁ (inj {n} {i} s)

creverse : cList ⇒ cList
creverse = idₛ , rev-pos
  where rev-pos : {n : ℕ} → Fin n → Fin n
        rev-pos {zero} ()
        rev-pos {suc n} i = inj {n} {i} (n ℕ- i) 

\end{code}
%</creverse>


--Composition Example

%<*maybeSthg>
\begin{code}
cMaybeSthg : Cont → Cont
cMaybeSthg C = Compose cMaybe C
\end{code}
%</maybeSthg>

%<*maybeList>
\begin{code}
MaybeList : Set → Set
MaybeList = ⟦ cMaybeSthg cList ⟧ 
\end{code}
%</maybeList>

%<*maybeListconstr>
\begin{code}
nolist : ∀{X} → MaybeList X
nolist = (false , (λ ())) , (λ { (() , _) })

justnil : ∀{X} → MaybeList X
justnil = (true , (λ { tt → 0 } )) , (λ { (tt , ()) })

justcons : ∀{X} → X → MaybeList X → MaybeList X
justcons x ((false , s) , f) = nolist
justcons x ((true , s) , f) with inspect s tt
justcons x ((true , s) , f) | [ refl ]ᵢ = ((true , (λ { tt → suc (s tt)}) )) , (λ { (tt , zero) → x ; (tt , suc i) → f (tt , i) })
\end{code}
%</maybeListconstr>


--Coproduct Example


%<*errorMes>
\begin{code}
errorMes :  ∀{C : Cont}{Str : Set}
            → Str
            → Compose cMaybe C ⇒ Either C (cK Str)
errorMes s =  (λ  {  (false  , _)     → inj₂ s
                  ;  (true   , c)     → inj₁ (c tt) }),
              (λ  {  {false  , _}  ()
                  ;  {true   , _}  x  → tt , x })
\end{code}
%</errorMes>

--Product Example


\begin{code}
data [_] (A : Set) : Set where
  [] : [ A ]
  _∷_ : A → [ A ] → [ A ] 
\end{code}

%<*tolist>
\begin{code}
ListTo[] : ∀{A} → List A → [ A ]
ListTo[] (zero , p) = []
ListTo[] (suc s , p) =  p zero ∷ (ListTo[] (s , (λ i → p (suc i))))
\end{code}
%</tolist>

%<*splitFin>
\begin{code}
splitFin : {n₁ n₂ : ℕ}(i : Fin (n₁ + n₂)) → Fin n₁ ⊎ Fin n₂
splitFin {zero}    i        = inj₂ i
splitFin {suc n₁}  zero     = inj₁ zero
splitFin {suc n₁}  (suc i)  = map suc idₛ (splitFin i)
\end{code}
%</splitFin>


%<*appendt>
\begin{code}
append : Both cList cList ⇒ cList
\end{code}
%</appendt>

--if i < n₁ then inj₁ i else inj₂ (i - n₁)
%<*appendd>
\begin{code}
append = ( uncurry _+_ ) , splitFin
\end{code}
%</appendd>
%<*ll>
\begin{code}
ceroAdos,tresAsiete : ⟦ Both cList cList ⟧ ℕ
ceroAdos,tresAsiete = (3 , 5) , (λ  {  (inj₁ x) → toℕ x
                                    ;  (inj₂ y) → ( 3 + toℕ y ) })
\end{code}
%</ll>

%<*l>
\begin{code}
ceroAsiete : ⟦ cList ⟧ ℕ 
ceroAsiete = ⟦ append ⟧ₘ ceroAdos,tresAsiete
\end{code}
%</l>


--Exponential Examples


%<*curryappend>
\begin{code}
curryappend  : cList ⇒ cList ^ cList
curryappend  =  (λ n₁ → (λ n₂ → n₁ + n₂ , eraseLeft ∘ₛ splitFin {n₁}) )
             ,  (λ { {n₁} (n₂ , q , p) → fromInj₁ (splitFin q) p })
\end{code}
%</curryappend>
