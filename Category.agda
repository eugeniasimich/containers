module Category where

open import Extras

record Category {o a} : Set (lsuc (o ⊔ a)) where
  field  Obj   :  Set o
         Hom   :  Obj → Obj → Set a
         iden  :  ∀{A} → Hom A A
         comp  :  ∀{A B C} → Hom B C → Hom A B → Hom A C
         idl   :  ∀{A B}{f : Hom A B} → comp iden f ≅ f
         idr   :  ∀{A B}{f : Hom A B} → comp f iden ≅ f
         ass   :  ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
               →  comp h (comp g f) ≅ comp (comp h g) f

open Category

_ᴼᵖ : ∀{o a} → Category {o}{a} → Category
𝓒 ᴼᵖ = record
    { Obj   = Obj 𝓒
    ; Hom   = λ A B → Hom 𝓒 B A
    ; iden  = iden 𝓒
    ; comp  = λ {A} {B} {C} f g → comp 𝓒 g f
    ; idl   = idr 𝓒
    ; idr   = idl 𝓒
    ; ass   = sym (ass 𝓒)
    }
