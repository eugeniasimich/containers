\begin{code}
module Agda where
open import Data.Nat
\end{code}

%<*bool>
\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool
\end{code}
%</bool>

\begin{code}
if_then_else_ : ∀{A : Set} → Bool → A → A → A
if true then a else b = a
if false then a else b = b
\end{code}

%<*idbool>
\begin{code}
idbool : Bool → Bool
idbool x = x
\end{code}
%</idbool>

%<*eqbool>
\begin{code}
eqbool : Bool → Bool → Bool
eqbool true true     = true
eqbool false false   = true
eqbool _ _           = false
\end{code}
%</eqbool>

%<*nat>
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat → Nat
\end{code}
%</nat>

%<*idnat>
\begin{code}
idnat : Nat → Nat
idnat x = x
\end{code}
%</idnat>

%<*eqnat>
\begin{code}
eqnat : Nat → Nat → Bool
eqnat zero zero        = true
eqnat zero (suc _)     = false
eqnat (suc _) zero     = false
eqnat (suc x) (suc y)  = eqnat x y
\end{code}
%</eqnat>

%<*id>
\begin{code}
id : ∀{A : Set} → A → A
id x = x
\end{code}
%</id>

%<*Name>
\begin{code}
data Name : Set where
  nat   : Name
  bool  : Name
\end{code}
%</Name>

%<*Nameext>
\begin{code}
⟦_⟧ : Name → Set
⟦ nat ⟧   = Nat
⟦ bool ⟧  = Bool
\end{code}
%</Nameext>

%<*eqt>
\begin{code}
eq : (c : Name) → ⟦ c ⟧ → ⟦ c ⟧ → Bool
\end{code}
%</eqt>

%<*eqd>
\begin{code}
eq nat   = eqnat
eq bool  = eqbool 
\end{code}
%</eqd>


%<*list>
\begin{code}
data List (X : Set) : Set where
  nil   : List X
  cons  : X → List X  → List X 
\end{code}
%</list>

%<*elem>
\begin{code}
elem? : {c : Name} → ⟦ c ⟧ → List ⟦ c ⟧ → Bool
\end{code}
%</elem>

\begin{code}
elem? {c} x nil         = false
elem? {c} x (cons y l)  = if eq c x y then true else elem? x l
\end{code}


%<*maplist>
\begin{code}
maplist : ∀{A B} → (A → B) → List A → List B
maplist f nil         = nil
maplist f (cons x l)  = cons (f x) (maplist f l) 
\end{code}
%</maplist>

%<*maybe>
\begin{code}
data Maybe (X : Set) : Set where
  nothing  : Maybe X
  just     : X → Maybe X
\end{code}
%</maybe>

%<*mapmaybe>
\begin{code}
mapmaybe : ∀{A B} → (A → B) → Maybe A → Maybe B
mapmaybe f nothing = nothing
mapmaybe f (just x) = just (f x)
\end{code}
%</mapmaybe>

%<*tree>
\begin{code}
data Tree (X : Set) : Set where
  leaf  : X → Tree X
  node  : Tree X → Tree X → Tree X
\end{code}
%</tree>

%<*maptree>
\begin{code}
maptree : ∀{A B} → (A → B) → Tree A → Tree B
maptree f (leaf x)    = leaf (f x)
maptree f (node l r)  = node (maptree f l) (maptree f r)
\end{code}
%</maptree>

%<*stream>
\begin{code}
data Stream (A : Set) : Set where
  cons :  A → Stream A → Stream A
\end{code}
%</stream>


%<*mapstream>
\begin{code}
mapstream : ∀{A B} → (A → B) → Stream A → Stream B
mapstream f (cons x s) = cons (f x) (mapstream f s)
\end{code}
%</mapstream>



%<*bot>
\begin{code}
data ⊥ : Set where
\end{code}
%</bot>

%<*top>
\begin{code}
data Unit : Set where
  tt : Unit
\end{code}
%</top>

%<*Fin>
\begin{code}
data Fin :  ℕ → Set where
   zero  : {n : ℕ} → Fin (suc n)
   suc   : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
%</Fin>


%<*not>
\begin{code}
not : Bool → Bool
not true   = false
not false  = true
\end{code}
%</not>

%<*and>
\begin{code}
and : Bool → Bool → Bool
and = λ  { true   y  → y
         ; false  _  → false }
\end{code}
%</and>


%<*empty>
\begin{code}
empty : ∀{X : Set} → ⊥ → X
empty ()
\end{code}
%</empty>

%<*sigma>
\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
\end{code}
%</sigma>

%<*syntax>
\begin{code}
syntax Σ A (λ x → B) = Σ[ x ∈ A ] B
\end{code}
%</syntax>

%<*times>
\begin{code}
data _×_ (X Y : Set) : Set where
  _,_ : X → Y → X × Y
\end{code}
%</times>

%<*proj1>
\begin{code}
proj₁ : ∀{X Y} → X × Y → X
proj₁ (x , y) = x
\end{code}
%</proj1>

%<*plus>
\begin{code}
data _⊎_ (X Y : Set) : Set where
  inj₁ : X → X ⊎ Y
  inj₂ : Y → X ⊎ Y
\end{code}
%</plus>


%<*id>
\begin{code}
data Id (X : Set) : Set where
  identity : X → Id X
\end{code}
%</id>


%<*reader>
\begin{code}
data Reader (E : Set) (X : Set) : Set where
  reader : (E → X) → Reader E X
\end{code}
%</reader>

%<*head>
\begin{code}
head : ∀{X} → List X → Maybe X
head nil = nothing
head (cons x l) = just x
\end{code}
%</head>

\begin{code}
data F (X : Set) : Set where
  idF : X → F X
\end{code}

%<*map>
\begin{code}
map : ∀ {A B} → (A → B) → F A → F B
\end{code}
%</map>

\begin{code}
map f (idF x) = idF (f x)
\end{code}

