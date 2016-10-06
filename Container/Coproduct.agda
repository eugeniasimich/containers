module Container.Coproduct where

open import Container
open import Category.Coproduct
open import Data.Sum renaming ([_,_] to [_,_]ₛ)
open import Extras


Either : ∀{a} → Container {a} → Container → Container 
Either C D = (Sh C ⊎ Sh D) ◃ [ Pos C , Pos D ]ₛ

ι₁ : ∀{l}{C D : Container {l}} → C ⇒ Either C D
ι₁ = inj₁ , idₛ

ι₂ : ∀{l}{C D : Container {l}} → D ⇒ Either C D
ι₂ = inj₂ , idₛ

[_,_] : ∀{l}{A B C : Container {l}} → (A ⇒ C) → (B ⇒ C) → (Either A B ⇒ C)
[ f , g ] = [ mSh f , mSh g ]ₛ  ,  (λ {  {inj₁ x}  →  mPos f {x}
                                ;        {inj₂ y}  →  mPos g {y} })

[_,_]∘ι₁≅f  : ∀ {l}{A B C : Container {l}}
            → (f : A ⇒ C)
            → (g : B ⇒ C)
            → [ f , g ] ∘ ι₁ ≅ f
[ f , g ]∘ι₁≅f  = refl

[_,_]∘ι₂≅g : ∀ {l}{A B C : Container {l}}
           → (f : A ⇒ C)
           → (g : B ⇒ C)
           → [ f , g ] ∘ ι₂ ≅ g
[ f , g ]∘ι₂≅g = refl

copairUnique◂  : ∀{l}{A B C : Container {l}}
               → {f : A ⇒ C}
               → {g : B ⇒ C}
               → {h : Either A B ⇒ C}
               → h ∘ ι₁  ≅ f
               → h ∘ ι₂  ≅ g
               → h ≅ [ f , g ]
copairUnique◂  refl refl = mEq
                          (ext   ( λ  {  (inj₁ _) → refl
                                      ;  (inj₂ _) → refl }))
                          (iext  ( λ  {  {inj₁ _} → ext (λ _ → refl)
                                      ;  {inj₂ _} → refl }))

ContHasCoproducts : ∀{l} → HasCoproducts {lsuc l} 𝑪𝒐𝒏𝒕
ContHasCoproducts = record
            { Coprod        = Either
            ; inl           = ι₁
            ; inr           = ι₂
            ; copair        = [_,_]
            ; copairIdl     = λ f g → [ f , g ]∘ι₁≅f
            ; copairIdr     = λ f g → [ f , g ]∘ι₂≅g
            ; copairUnique  = copairUnique◂
            }
