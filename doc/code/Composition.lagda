
\begin{code}
module Composition where

open import Container
open import Data.Product
--open import Function --renaming (_∘_ to _∘̲_ ; id to i̲d̲ )

open Cont
\end{code}

%<*compose>
\begin{code}
Compose : Cont → Cont → Cont
Compose C D = ⟦ C ⟧ (Sh D) ◃ (λ {  (c , d) →
                                   Σ[ p ∈ Pos C c ] Pos D (d p)})
\end{code}
%</compose>


