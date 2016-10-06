module Container.Composition where

open import Container
open import Extras

open Container.Container

Compose : ∀{l} → Container {l} → Container → Container
Compose C D = ⟦ C ⟧ (Sh D) ◃ (λ {  (c , d) →
                                   Σ[ p ∈ Pos C c ] Pos D (d p)})


