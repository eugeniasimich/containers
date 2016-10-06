module Container where

open import Extras
open import Category

record Container {l}: Set (lsuc l) where
  constructor _◃_
  field
    Sh  : Set l
    Pos : Sh → Set l

open Container public

⟦_⟧ : ∀{l} → Container {l} → Set l → Set l 
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

record _⇒_ {l} (C D : Container {l}) : Set l where
  constructor _,_
  field
    mSh  : Sh C → Sh D
    mPos : ∀{s : Sh C} → Pos D (mSh s) → Pos C s

infixr 4 _⇒_
open _⇒_ public

_∘_ : ∀{l}{A B C : Container {l}} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
g ∘ f = (mSh g ∘ₛ mSh f) , (mPos f ∘ₛ mPos g)

id : ∀{l}{C : Container {l}} → C ⇒ C
id = idₛ , idₛ

⟦_⟧ₘ : ∀{l}{C D : Container {l}} → (C ⇒ D) → ∀{X} → ⟦ C ⟧ X → ⟦ D ⟧ X
⟦ f ⟧ₘ ( c , fp ) = (mSh f c) , (fp ∘ₛ mPos f {c})

mEq :  ∀{l}{A B : Container {l}}{f g : A ⇒ B}
    →  mSh f ≅ mSh g
    →  (λ {s} → mPos f {s}) ≅ (λ {s} → mPos g {s})
    →  f ≅ g
mEq refl refl = refl


𝑪𝒐𝒏𝒕 : ∀{l} → Category {lsuc l}
𝑪𝒐𝒏𝒕 {l} = record
            { Obj   = Container 
            ; Hom   = _⇒_
            ; iden  = id
            ; comp  = _∘_
            ; idl   = refl
            ; idr   = refl
            ; ass   = refl
            }
