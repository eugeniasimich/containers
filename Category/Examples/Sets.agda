module Category.Examples.Sets where

open import Extras
open import Category
open import Category.Product
open import Category.Coproduct
open import Category.Initial
open import Category.Terminal
open import Category.Exponential
open import Function renaming (_∘_ to composition ; _∘′_ to _∘_)

𝑺𝒆𝒕 : ∀{l} → Category {lsuc l}
𝑺𝒆𝒕 {l} = record
           { Obj   = Set l
           ; Hom   = λ R S → R → S
           ; iden  = id
           ; comp  = _∘_
           ; idl   = refl
           ; idr   = refl
           ; ass   = refl
           }


SetHasProducts : HasProducts 𝑺𝒆𝒕
SetHasProducts = record
      { Prod        = _×_
      ; projl       = proj₁
      ; projr       = proj₂
      ; pair        = <_,_>
      ; pairIdl     = λ f g → refl
      ; pairIdr     = λ f g → refl
      ; pairUnique  = pairUniqueₛ }
  where pairUniqueₛ  :  ∀{X Y Z : Set}{f : X → Y}{g : X → Z}
                     →  ∀{h} → proj₁ ∘ h ≅ f
                     →  proj₂ ∘ h ≅ g
                     →  h ≅ < f , g >
        pairUniqueₛ refl refl = refl

SetHasCoproducts : HasCoproducts 𝑺𝒆𝒕
SetHasCoproducts = record
      { Coprod        = _⊎_
      ; inl           = inj₁
      ; inr           = inj₂
      ; copair        = [_,_]ₛ
      ; copairIdl     = λ f g → refl
      ; copairIdr     = λ f g → refl
      ; copairUnique  = copairUniqueₛ }
        where copairUniqueₛ  :  ∀{X Y Z : Set}{f : Y → X}{g : Z → X}
                             →  ∀{h}
                             →  h ∘ inj₁ ≅ f
                             →  h ∘ inj₂ ≅ g
                             →  h ≅ [ f , g ]ₛ
              copairUniqueₛ refl refl = ext (λ  {  (inj₁ _) → refl
                                                ;  (inj₂ _) → refl })

SetHasInitial : HasInitial 𝑺𝒆𝒕
SetHasInitial = record
  { Initial = ⊥
  ; fromInitMor = λ { () }
  ; isUniqueFromInitMor = ext (λ { () })
  } 

SetHasTerminal : HasTerminal 𝑺𝒆𝒕
SetHasTerminal = record
    { Terminal = ⊤
    ; toTermMor = λ _ → tt
    ; isUniqueToTermMor = refl
    }

SetHasExponentials : HasExponentials 𝑺𝒆𝒕 SetHasProducts
SetHasExponentials = record
    { Exp = λ x y → y → x
    ; floor = λ f x y → f (x , y)
    ; ceil = λ { f (x , y) → f x y }
    ; iso₁ = refl
    ; iso₂ = refl
    ; nat = λ g f → refl
    }
