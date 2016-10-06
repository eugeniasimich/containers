
\begin{code}
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Empty
\end{code}

\begin{code}
¬ : Set → Set
¬ A = A → ⊥
\end{code}

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

%<*positive>
\begin{code}
positiveNat : Set
positiveNat = Σ[ n ∈ ℕ ] (¬ (n ≡ zero))

one : positiveNat
one = (suc zero , λ ())
\end{code}
%</positive>

