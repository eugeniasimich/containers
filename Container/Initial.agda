module Container.Initial where

open import Container
open import Extras
open import Category.Initial

Zero : Container
Zero = ⊥ ◃ (λ _ → ⊥)

Zeroₘ : ∀{C} → Zero ⇒ C
Zeroₘ = (λ { () }) , (λ {})

ZeroₘUnique  : ∀{C}
             → {f : Zero ⇒ C}
             → Zeroₘ {C} ≅ f 
ZeroₘUnique  = mEq  (ext      (λ ()))
                    (iext  (λ {  }))

ContHasInitial : HasInitial 𝑪𝒐𝒏𝒕
ContHasInitial = record
            { Initial              = Zero
            ; fromInitMor          = Zeroₘ
            ; isUniqueFromInitMor  = ZeroₘUnique }
