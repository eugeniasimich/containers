open import Category
open import Extras

module Category.Product {o a : Level} (𝓒 : Category {o} {a}) where

open import Relation.Binary.HeterogeneousEquality
open Category.Category

record HasProducts : Set (o ⊔ a) where
  field
    Prod   : Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    projl   : ∀{X Y} → Hom 𝓒 (Prod X Y) X
    projr   : ∀{X Y} → Hom 𝓒 (Prod X Y) Y
    pair    : ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
            → Hom 𝓒 Z (Prod X Y)

  pmap  : ∀{X X' Y Y'}
        → (f : Hom 𝓒 X X')(g : Hom 𝓒 Y Y')
        → Hom 𝓒 (Prod X Y) (Prod X' Y')
  pmap f g = pair (comp 𝓒 f projl) (comp 𝓒 g projr)

  field
    pairIdl     :  ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
                   → comp 𝓒 projl (pair f g) ≅ f  
    pairIdr     :  ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
                   → comp 𝓒 projr (pair f g) ≅ g  
    pairUnique  :  ∀{X Y Z}{f : Hom 𝓒 X Y}{g : Hom 𝓒 X Z}
                   → {h : Hom 𝓒 X (Prod Y Z)}
                   → (p₁ : comp 𝓒 projl h ≅ f)
                   → (p₂ : comp 𝓒 projr h ≅ g)
                   →  h ≅ (pair f g)
