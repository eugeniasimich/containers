\begin{code}
open import Coinduction
open import Data.Nat
open import Function
\end{code}

%<*stream>
\begin{code}
data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A
\end{code}
%</stream>

%<*stream1s>
\begin{code}
s : Stream ℕ
s = 1 ∷ ♯ s 
\end{code}
%</stream1s>

%<*streamCons>
\begin{code}
streamCons : ∀{A} → (ℕ → A) → Stream A
streamCons f = f 0 ∷ ♯ streamCons (f ∘ suc)
\end{code}
%</streamCons>

