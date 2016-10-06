
\begin{code}
module FunctorContainer where

open import Container
open import Function
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Extras
open Cont
\end{code}


\begin{code}
map-id : ∀{C X} → map {X} {X} {C} id ≅ id {A = ⟦ C ⟧ X}
map-id = ext (λ _ → dSumEq refl refl refl)

map-∘ : ∀{C X Y Z}{f : Z →  Y}{g : X →  Z } → (map f) ∘ (map {C = C} g)  ≅ map {C = C} (f ∘ g) 
map-∘ {f} {g} = ext (λ _ → dSumEq refl refl refl)
\end{code}
