open import Category
open import Category.Product
open import Extras

module Category.Exponential {o a : Level}(𝓒 : Category {o} {a}) (pr : HasProducts 𝓒) where

open Category.Category

record HasExponentials : Set (o ⊔ a) where
  open HasProducts
  field
    Exp     :  Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    floor   :  ∀{X Y Z}
            →  Hom 𝓒 (Prod pr X Y) Z
            →  Hom 𝓒 X (Exp Z Y)
    ceil    :  ∀{X Y Z}
            →  Hom 𝓒 X (Exp Z Y)
            →  Hom 𝓒 (Prod pr  X Y) Z
    iso₁    :  ∀{X Y Z}{f : Hom 𝓒 (Prod pr X Y) Z}
            →  ceil (floor f) ≅ f
    iso₂    :  ∀{X Y Z}{f : Hom 𝓒 X (Exp Z Y)}
            →  floor (ceil f) ≅ f
    nat     :  ∀{X X' Y Z : Obj 𝓒}
            →  (g : Hom 𝓒 (Prod pr X Y) Z)
            →  (f : Hom 𝓒 X' X)
            →  floor (comp 𝓒 g (pmap pr f (iden 𝓒))) ≅ comp 𝓒 (floor g) f

