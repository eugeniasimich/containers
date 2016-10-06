\begin{code}

module NegNeg where

open import Relation.Binary.HeterogeneousEquality
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Function
\end{code}

%<*neg>
\begin{code}
¬ : ∀{l} → Set l → Set l
¬ A = A → ⊥
\end{code}
%</neg>

\begin{code}
q : ∀{A : Set} → A ≅ ¬ (¬ A)
q = {!!}

p : ∀{A : Set} → ¬ ( A ≅ ¬ (¬ A))
p = λ { x → {!x!} }

a : ∀{A : Set} → ¬( ¬ (A ⊎ ¬ A))
a {A} = λ {x → case x _ of (λ { () })}
\end{code}
