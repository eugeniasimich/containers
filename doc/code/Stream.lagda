\begin{code}
open import Data.Nat
open import Function
\end{code}

%<*stream>
\begin{code}
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
\end{code}
%</stream>

\begin{code}
open Stream
\end{code}

%<*stream1s>
\begin{code}
s : Stream ℕ
hd s = 1
tl s = s
\end{code}
%</stream1s>


