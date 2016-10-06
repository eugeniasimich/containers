open import Category
open import Extras

module Category.Terminal {o a : Level} (𝓒 : Category {o} {a}) where

open import Relation.Binary.HeterogeneousEquality
open Category.Category

record HasTerminal : Set (o ⊔ a) where
  field
    Terminal            :  Obj 𝓒
    toTermMor           :  ∀{X} → Hom 𝓒 X Terminal 
    isUniqueToTermMor   :  ∀{X}{f : Hom 𝓒 X Terminal}
                        →  toTermMor {X} ≅ f
