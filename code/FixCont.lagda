
\begin{code}

module FixCont where
open import Container renaming (map to mapc)
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Sum renaming ([_,_] to [_,_]𝓢et)
open import Function renaming (_∘_ to _∘̂_ ; id to idₛ)
open Cont
open _⇒_
\end{code}

\begin{code}
data μ (C : Cont) : Set where
 ⟪_⟫ : ⟦ C ⟧ (μ C) → μ C
\end{code}

\begin{code}
cTree₂ : Set → Cont
cTree₂ A = Either (cK A) (Both cId cId)
\end{code}

\begin{code}
Tree₂ : Set → Set
Tree₂ A = μ (cTree₂ A)

mapT : ∀{A B} → (A → B) → Tree₂ A → Tree₂ B
mapT f ⟪ inj₁ x , p ⟫ = ⟪ (inj₁ (f x) , (λ { () })) ⟫
mapT f ⟪ inj₂ (tt , tt) , p ⟫ = ⟪ (inj₂ (tt , tt) , (λ { s → mapT f (p s)})) ⟫
\end{code}

\begin{code}
leaf₂ : {A : Set} → A → Tree₂ A
leaf₂ a = ⟪ (inj₁ a) , (λ () ) ⟫
\end{code}

\begin{code}
node₂ : {A : Set} → Tree₂ A → Tree₂ A → Tree₂ A
node₂ l r = ⟪ (inj₂ (tt , tt)) , (λ  {  (inj₁ tt) → r
                                     ;  (inj₂ tt) → l }) ⟫
\end{code}