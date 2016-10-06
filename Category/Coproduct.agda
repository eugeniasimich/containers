open import Category
open import Extras hiding (_,_) 

module Category.Coproduct {o a : Level} (𝓒 : Category {o} {a}) where

open import Data.Sum hiding ([_,_])
open Category.Category

record HasCoproducts : Set (o ⊔ a) where
  field
    Coprod         :  Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    inl            :  ∀{X Y} → Hom 𝓒 X (Coprod X Y)
    inr            :  ∀{X Y} → Hom 𝓒 Y (Coprod X Y) 
    copair         :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  Hom 𝓒 (Coprod X Y) Z
    copairIdl      :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  comp 𝓒 (copair f g) inl ≅ f  
    copairIdr      :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  comp 𝓒 (copair f g) inr ≅ g  
    copairUnique   :  ∀{X Y Z}{f : Hom 𝓒 X Z}{g : Hom 𝓒 Y Z}
                      {h : Hom 𝓒 (Coprod X Y) Z}
                   →  (p₁ : comp 𝓒 h inl ≅ f)
                   →  (p₂ : comp 𝓒 h inr ≅ g)
                   →  h ≅ copair f g
  
