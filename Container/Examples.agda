module Container.Examples where

open import Container
open import Extras
open import Data.Nat
open import Data.Fin
open import Data.Bool
open Container.Container

--List container

cList : Container
cList = ℕ ◃ Fin

List : Set → Set
List = ⟦ cList ⟧

nil : ∀{X} → List X
nil = 0 , (λ ())

cons : ∀{X} → X → List X → List X
cons x (s , f) = suc s , (λ { zero → x ; (suc i) → f i })

--Identity container

cId : Container
cId = ⊤ ◃ (λ _ → ⊤ )

Id : Set → Set
Id = ⟦ cId ⟧

identity : ∀{X} → X → Id X
identity x = tt , (λ _ → x)


--Constant container

cK : Set → Container
cK A = A ◃ (λ _ → ⊥)

K : Set → Set → Set
K A = ⟦ cK A ⟧

dos : K ℕ ⊥
dos = 2 , (λ { () })

--Maybe container

cMaybe : Container
cMaybe = Bool ◃ (λ { false → ⊥ ; true → ⊤ }) 

Maybe : Set → Set
Maybe = ⟦ cMaybe ⟧

nothing : ∀{X} → Maybe X
nothing = false , (λ { () })

just : ∀{X} → X → Maybe X
just x = true , (λ { tt → x })


--Writer container
cWriter : Set → Container
cWriter W = W ◃ (λ w → ⊤)

Writer : Set → Set → Set
Writer W = ⟦ cWriter W ⟧ 

--Reader container

cReader : Set → Container
cReader E = ⊤ ◃ (λ {tt → E})

Reader : Set → Set → Set
Reader E = ⟦ cReader E ⟧ 

reader : ∀{E X} → (E → X) → Reader E X
reader x = tt , x


runReader : ∀{E X} → Reader E X → E → X
runReader  (tt , f) x = f x

ask : ∀{E} → Reader E E
ask = tt , (λ z → z)

returnReader : ∀{E X} → X → Reader E X
returnReader x = tt , (λ _ → x)

>>=Reader : ∀{E X Y} → Reader E X → (X → Reader E Y) → Reader E Y
>>=Reader r f = tt , (λ x → runReader (f (runReader r x)) x)

--State container

cState : Set → Container
cState S = (S → S) ◃ (λ x → S)

State : Set → Set → Set
State S = ⟦ cState S ⟧ 

runState : ∀{S X} → State S X → S → X × S
runState (s , f) st = (f st) , (s st)

put : ∀{S} → S →  State S ⊤
put s = (λ x → s) , (λ _ → tt)

get : ∀{S} → State S S
get = (λ x → x) , (λ x → x)

--Stream container

cStream : Container
cStream = ⊤ ◃ (λ {tt → ℕ})

Stream : Set → Set
Stream = ⟦ cStream ⟧

--Tree container

data TreeSh : Set where
  leafSh : TreeSh
  nodeSh : TreeSh → TreeSh → TreeSh

data TreePos : TreeSh → Set where
  leafPos : TreePos leafSh
  nodePosL : ∀{l r} → TreePos l → TreePos (nodeSh l r)  
  nodePosR : ∀{l r} → TreePos r → TreePos (nodeSh l r)  

cTree : Container
cTree = TreeSh ◃ TreePos

Tree : Set → Set
Tree = ⟦ cTree ⟧

leaf : ∀{X} → X →  ⟦ cTree ⟧ X
leaf x = leafSh , (λ { leafPos → x })

node : ∀{X} → Tree X → Tree X → Tree X
node (sl , pl) (sr , pr) = nodeSh sl sr , (λ  { (nodePosL pos) → pl pos
                                              ; (nodePosR pos) → pr pos })

