open import Category
open import Extras

module Category.Isomorphism {o a : Level}{𝓒 : Category{o}{a}} where

open import Relation.Binary.HeterogeneousEquality

open Category.Category

record IsIsomorphism {A B : Obj 𝓒}(f : Hom 𝓒 A B) : Set a where
  field
    inverse : Hom 𝓒 B A
    iso₁ : comp 𝓒 f inverse ≅ iden 𝓒 {B}
    iso₂ : comp 𝓒 inverse f ≅ iden 𝓒 {A}
