\begin{code}
module Universos where

open import Data.Bool
open import Data.Nat
open import Aux
\end{code}

%<*codes>
\begin{code}
data U₁ : Set where
  booleanos  : U₁
  naturales  : U₁
\end{code}
%</codes>

%<*extension>
\begin{code}
⟦_⟧₁ : U₁ → Set
⟦ booleanos  ⟧₁ = Bool
⟦ naturales  ⟧₁ = ℕ
\end{code}
%</extension>

%<*codes2>
\begin{code}
data U₂ : Set where
  listas   : U₂
  arboles  : U₂
\end{code}
%</codes2>

%<*extension2>
\begin{code}
⟦_⟧₂ : U₂ → Set → Set
⟦ listas   ⟧₂ = List
⟦ arboles  ⟧₂ = Tree
\end{code}
%</extension2>
