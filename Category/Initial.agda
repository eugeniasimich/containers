open import Category
open import Extras

module Category.Initial {o a : Level} (𝓒 : Category {o} {a}) where

open import Relation.Binary.HeterogeneousEquality
open Category.Category

record HasInitial : Set (o ⊔ a) where
  field
    Initial               :  Obj 𝓒
    fromInitMor           :  ∀{X} → Hom 𝓒 Initial X 
    isUniqueFromInitMor   :  ∀{X}{f : Hom 𝓒 Initial X}
                          →  fromInitMor {X} ≅ f
