open import Category
open import Extras

module Category.Funtor {o a o' a' : Level}(𝓒 : Category {o} {a}) (𝓓 : Category {o'} {a'}) where

open import Relation.Binary.HeterogeneousEquality
open Category.Category

record Functor : Set (o ⊔ a ⊔ o' ⊔ a') where
  field
    FObj      :  Obj 𝓒 → Obj 𝓓
    FHom      :  ∀{A B}
              →  Hom 𝓒 A B → Hom 𝓓 (FObj A) (FObj B)
    idenPr    :  ∀{A}
              →  FHom (iden 𝓒 {A}) ≅ iden 𝓓 {FObj A}
    compPr    :  ∀{A B C}{f : Hom 𝓒 A B}{g : Hom 𝓒 B C}
              →  FHom (comp 𝓒 g f) ≅ comp 𝓓 (FHom g) (FHom f)
