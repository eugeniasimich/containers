module Container.Product where

open import Container
open import Category.Product
open import Extras


Both : ∀{l} → Container {l} → Container {l} → Container {l}
Both C D = (Sh C × Sh D) ◃ (λ { (c , d) → Pos C c ⊎ Pos D d })

Π₁ : ∀{l}{C D : Container {l}} → (Both C D) ⇒ C
Π₁ = proj₁ , inj₁

Π₂ : ∀{l}{C D : Container {l}} → (Both C D) ⇒ D
Π₂ = proj₂ , inj₂

⟨_,_⟩ : ∀{l}{A B C : Container {l}} → (C ⇒ A) → (C ⇒ B) → (C ⇒ Both A B)
⟨ f , g ⟩ =  < mSh f , mSh g > , [ mPos f , mPos g ]ₛ

_×ₘ_ : ∀{l}{A B C D : Container {l}} →
         (f : A ⇒ B) →
         (g : C ⇒ D) →
         Both A C ⇒ Both B D
f ×ₘ g = ⟨ f ∘ Π₁ , g ∘ Π₂ ⟩

--proofs

Π₁∘⟨_,_⟩≅f      :  ∀{l}{A B C : Container {l}}(f : C ⇒ A)(g : C ⇒ B) 
                →  Π₁ ∘ ⟨ f , g ⟩ ≅ f
Π₁∘⟨ f , g ⟩≅f  = refl

Π₂∘⟨_,_⟩≅g      :  ∀{l}{A B C : Container {l}}(f : C ⇒ A)(g : C ⇒ B) 
                →  Π₂ ∘ ⟨ f , g ⟩ ≅ g
Π₂∘⟨ f , g ⟩≅g  = refl

pairUnique◂  :  ∀{l}{A B C : Container {l}}
             →  {f : C ⇒ A} 
             →  {g : C ⇒ B} 
             →  {h : C ⇒ Both A B}
             →  Π₁ ∘ h ≅ f 
             →  Π₂ ∘ h ≅ g
             →  h ≅ ⟨ f , g ⟩
pairUnique◂ {l} refl refl  = mEq
                             refl
                             (iext {l} (ext (λ  {  (inj₁ _) → refl
                                                ;  (inj₂ _) → refl })))

ContHasProducts : ∀{l} → HasProducts {lsuc l} 𝑪𝒐𝒏𝒕
ContHasProducts = record
            { Prod        = Both
            ; projl       = Π₁
            ; projr       = Π₂ 
            ; pair        = ⟨_,_⟩
            ; pairIdl     = λ f g → Π₁∘⟨ f , g ⟩≅f 
            ; pairIdr     = λ f g → Π₂∘⟨ f , g ⟩≅g
            ; pairUnique  = pairUnique◂
            }
