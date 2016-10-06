\begin{code}
module FunctorialContainers where

open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty
--open import Morphism
\end{code}


%<*cont>
\begin{code}
record Cont : Set₁ where
  constructor _▹_
  field
    Sh  : Set 
    Pos : Sh → Set 
\end{code}
%</cont>

\begin{code}
open Cont
--open _⇒_
\end{code}


%<*ext>
\begin{code}
⟦_⟧ : Cont → Set → Set 
⟦ S ▹ P ⟧ X = Σ[ s ∈ S ] (P s → X)
\end{code}
%</ext>

\begin{code}
1▹ : Cont
1▹ = ⊤ ▹ (λ _ → ⊥)
\end{code}

\begin{code}
cId : Cont
cId = ⊤ ▹ (λ _ → ⊤ )
\end{code}

\begin{code}
_×▹_ : Cont → Cont → Cont
C₁ ×▹ C₂ = (Sh C₁ × Sh C₂) ▹ (λ x → Pos C₁ (proj₁ x) ⊎ Pos C₂ (proj₂ x))
\end{code}

\begin{code}
_+▹_ : Cont → Cont → Cont
C₁ +▹ C₂ = (Sh C₁ ⊎ Sh C₂) ▹ [ Pos C₁ , Pos C₂ ]
\end{code}

\begin{code}
_∘▹_ : Cont → Cont → Cont
C₁ ∘▹ C₂ = ⟦ C₁ ⟧ (Sh C₂) ▹ (λ x → Σ[ p ∈ Pos C₁ (proj₁ x)] (Pos C₂ (proj₂ x p)) )
\end{code}

-- \begin{code}
-- μ▹_ : Cont → Cont
-- μ▹ C = C ∘▹ (μ▹ C)
-- \end{code}



\begin{code}
--cNat : Cont
--cNat = 1▹ +▹ cNat
\end{code}


%<*applicative-almost>
\begin{code}
<*> : ∀{X Y C} → (f : ⟦ C ⟧ (X → Y)) → ⟦ C ⟧ X → ⟦ C ∘▹ C ⟧ Y
<*> (sf , pf) (s , p) = (sf , (λ _ → s))  , (λ psf → pf (proj₁ psf) (p (proj₂ psf)))
\end{code}
%</applicative-almost>
