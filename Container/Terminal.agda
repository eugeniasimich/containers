module Container.Terminal where

open import Container
open import Category.Terminal
open import Extras


One : Container 
One = ⊤ ◃ (λ _ → ⊥)

Oneₘ : ∀{A} → A ⇒ One
Oneₘ = (λ _ → tt) , (λ ())

OneₘUnique  : {C : Container}
            → {f : C ⇒ One}
            → Oneₘ {C} ≅ f 
OneₘUnique = mEq refl (iext (ext (λ ()))) 

ContHasTerminal : HasTerminal 𝑪𝒐𝒏𝒕
ContHasTerminal = record
            { Terminal           = One
            ; toTermMor          = Oneₘ
            ; isUniqueToTermMor  = OneₘUnique }
