
\begin{code}
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Coinduction
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
\end{code}

%<*list>
\begin{code}
data List (X : Set) : Set where
  nil :  List X
  cons : X → List X  → List X 
\end{code}
%</list>

%<*fin>
\begin{code}
data Fin : ℕ → Set where
  zero :  ∀{n} → Fin (n + 1)
  suc  :  ∀{n} → Fin n → Fin (n + 1)  
\end{code}
%</fin>

%<*id>
\begin{code}
data Id (X : Set) : Set where
  identity : X → Id X
\end{code}
%</id>

%<*maybe>
\begin{code}
data Maybe (X : Set) : Set where
  nothing : Maybe X
  just    : X → Maybe X
\end{code}
%</maybe>

%<*writer>
\begin{code}
data Writer (W : Set) : Set → Set where
  writer : ∀{X} → (W × X) → Writer W X
\end{code}
%</writer>

%<*reader>
\begin{code}
data Reader (E : Set) (X : Set) : Set where
  reader : (E → X) → Reader E X
\end{code}
%</reader>

%<*state>
\begin{code}
data State (S : Set) (X : Set) : Set where
  state : (S → S × X) → State S X
\end{code}
%</state>

%<*stream>
\begin{code}
data Stream (A : Set) : Set where
  _∷_ :  A → Stream A → Stream A
\end{code}
%</stream>

%<*head>
\begin{code}
head : ∀{X} → List X → Maybe X
head nil = nothing
head (cons x l) = just x
\end{code}
%</head>

%<*pair>
\begin{code}
data Pair (X : Set) (Y : Set) : Set where
  _,_ : X → Y → Pair X Y
\end{code}
%</pair>

%<*pairNX>
\begin{code}
PairℕX : Set → Set
PairℕX = Pair ℕ
\end{code}
%</pairNX>

\begin{code}
data Not (X : Set) : Set where
  kill : (X → ⊥) → Not X

mapN : ∀{X Y} → (Y → X) → (Not X → Not Y)
mapN f (kill x) = kill (λ y → x (f y))
\end{code}

%<*endo>
\begin{code}
data Endo (X : Set) : Set where
  fun : (X → X) → Endo X
\end{code}
%</endo>

mapE : ∀{X Y} → (X → Y) → (Endo X → Endo Y)

%<*part>
\begin{code}
data Power (X : Set) : Set where
  ₓ : (X → Bool) → Power X 
\end{code}
%</part>

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

%<*tree>
\begin{code}
data Tree (X : Set) : Set where
  leaf : X → Tree X
  node : Tree X → Tree X → Tree X
\end{code}
%</tree>


%<*tree2>
\begin{code}
data Tree₂ (X : Set) : Set where
  leaf : Tree₂ X
  node : X → Tree₂ X → Tree₂ X → Tree₂ X
\end{code}
%</tree2>

%<*uplus>
\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
\end{code}
%</uplus>

%<*choice>
\begin{code}
[_,_] : ∀{A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
\end{code}
%</choice>
