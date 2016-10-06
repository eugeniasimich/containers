
\begin{code}

module FixCont where
open import Container
open import Morphism
open import Sum
open import Product
open import Composition
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Sum renaming ([_,_] to [_,_]𝓢et)
open import Function renaming (_∘_ to _∘̂_ ; id to idₛ)--renaming (flip to fflip)
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
