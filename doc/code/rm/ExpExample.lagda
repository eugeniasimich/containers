
\begin{code}

module ExpExample where
open import Container hiding (map)
open import Morphism
open import Exponential
open import ProductExamples
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Function renaming ( _∘_ to _∘ₛ_) 
open Cont
open _⇒_

\end{code}


%<*curryappend>
\begin{code}
curryappend  : cList ⇒ cList ^ cList
curryappend  =  (λ n₁ → (λ n₂ → n₁ + n₂ , eraseLeft ∘ₛ splitFin {n₁}) )
             ,  (λ { {n₁} (n₂ , q , p) → fromInj₁ (splitFin q) p })
\end{code}
%</curryappend>

