
\begin{code}
module Container where

open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty
open import Function renaming (_∘_ to _∘ₛ_ ; id to idₛ)
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Extras

\end{code}


%<*cont>
\begin{code}
record Cont : Set₁ where
  constructor _◃_
  field
    Sh  : Set 
    Pos : Sh → Set 
\end{code}
%</cont>

\begin{code}
open Cont
\end{code}


%<*ext>
\begin{code}
⟦_⟧ : Cont → Set → Set 
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)
\end{code}
%</ext>

%<*map>
\begin{code}
map : ∀{X Y C} → (f : X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f (s , p) = s , (f ∘ₛ p)
\end{code}
%</map>

%<*morph>
\begin{code}
record _⇒_ (C₁ C₂ : Cont) : Set where
  constructor _,_
  field
    mSh  : Sh C₁ → Sh C₂
    mPos : ∀{s : Sh C₁} → Pos C₂ (mSh s) → Pos C₁ s
\end{code}
%</morph>

\begin{code}
infixr 4 _⇒_
open _⇒_
\end{code}

%<*morphExt>
\begin{code}
⟦_⟧ₘ : ∀{C D} → (C ⇒ D) → ∀{X} → ⟦ C ⟧ X → ⟦ D ⟧ X
⟦ f ⟧ₘ ( c , fp ) = (mSh f c) , (fp ∘ₛ mPos f {c})
\end{code}
%</morphExt>

%<*morphComp>
\begin{code}
_∘_ : ∀{A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
g ∘ f = (mSh g ∘ₛ mSh f) , (mPos f ∘ₛ mPos g)
\end{code}
%</morphComp>

%<*morphId>
\begin{code}
id : ∀{C} → C ⇒ C
id = idₛ , idₛ
\end{code}
%</morphId>


%<*equivalence>
\begin{code}
mEq :  ∀{A B}{f g : A ⇒ B}
                    → mSh f ≅ mSh g
                    → (λ {s} → mPos f {s}) ≅ (λ {s} → mPos g {s})
                    →  f ≅ g
mEq refl refl = refl
\end{code}
%</equivalence>

