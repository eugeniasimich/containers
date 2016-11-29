module Container.Exponential where

open import Container
open import Container.Product
open import Category.Exponential
open import Extras
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


_^_ : ∀{l} → Container {l} → Container {l} → Container {l}
C ^ B  =  ((b : Sh B) → Σ[ c ∈ Sh C ] (Pos C c → ⊤ ⊎ Pos B b))
       ◃
          (λ f →  Σ[ b ∈ Sh B ] (Σ[ q ∈ Pos C (proj₁ (f b))]
                  (proj₂ (f b) q ≡ inj₁ tt)))

eraseLeft : ∀{a b}{A : Set a}{B : Set b} → A ⊎ B → ⊤ ⊎ B
eraseLeft (inj₁ x) = inj₁ tt
eraseLeft (inj₂ y) = inj₂ y

fromInj₁ : ∀{a b}{A : Set a}{B : Set b} → (x : A ⊎ B) → (eraseLeft x ≡ inj₁ tt) →  A
fromInj₁ (inj₁ x) pr = x
fromInj₁ (inj₂ y) ()

insLeft : ∀{a b}{A : Set a}{B : Set b} → (x : ⊤ ⊎ B) → (x ≡ inj₁ tt → A) → A ⊎ B
insLeft (inj₁ _) pr = inj₁ (pr refl)
insLeft (inj₂ y) pr = inj₂ y

curry : ∀{l}{A B C : Container {l}} → (Both A B) ⇒ C → A ⇒ (C ^ B)
curry f = (λ a b → mSh f (a , b) , eraseLeft ∘ₛ (mPos f) ),
        (λ { {a} (b , c , r) → fromInj₁ (mPos f {a , b} c) r })

uncurry : ∀{l}{A B C : Container {l}} → A ⇒ (C ^ B) → Both A B ⇒ C
uncurry f  = proj₁ ∘ₛ uncurryₛ (mSh f) , 
        (λ { {a , b} c → insLeft (proj₂ (mSh f a b) c) (λ pr → (mPos f {a} (b , c , pr ))) })

^map : ∀{l}{A B C C' : Container {l}} → (f : C ⇒ C') → (h : A ⇒ C ^ B) → A ⇒ C' ^ B
^map f h = curry (f ∘ uncurry h)

--auxiliary proofs

lema₁ :  ∀{a b}{A : Set a}{B : Set b}
      →  {x : A ⊎ B} 
      →  insLeft (eraseLeft x) (fromInj₁ x) ≅ x
lema₁ {x = inj₁ x} = refl
lema₁ {x = inj₂ y} = refl

lema₂  :  ∀{a b}{A : Set a}{B : Set b}
       →  {x : ⊤ ⊎ B}
       →  {f : x ≡ inj₁ tt → A}
       →  eraseLeft (insLeft x f) ≅ x
lema₂ {x = inj₁ x} = refl
lema₂ {x = inj₂ y} = refl

lema₃  :  ∀{a b}{A : Set a}{B : Set b}
       →  {y : ⊤ ⊎ B}
       →  {f : y ≡ inj₁ tt → A }
       → fromInj₁ (insLeft y f) ≅ f
lema₃ {y = inj₁ tt}  = dext (λ  { {a = refl} {refl} _ → refl })
lema₃ {y = inj₂ _}   = ext (λ { () })

uncurryEq  :  ∀{a b c}{A : Set a} {B B' : A → Set b} {C : Set c}
           →  {f : (p : Σ A B) → C } {g : (p : Σ A B') → C}
           →  B ≅ B' → curryₛ f ≅ curryₛ g → f ≅ g
uncurryEq refl p = dcong uncurryₛ p refl refl 

lema₄  :  ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f : A → C}{x : A ⊎ B}
       →  eraseLeft (mapₛ f idₛ x) ≅ eraseLeft x 
lema₄ {x = inj₁ x} = refl
lema₄ {x = inj₂ y} = refl

lema₅ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f : A → C}{x : A ⊎ B}{p2}
   →  {p1 : eraseLeft (mapₛ f idₛ x) ≡ inj₁ tt}
   →  (fromInj₁ ∘ₛ mapₛ f idₛ) x p1 ≅ f (fromInj₁ x p2)
lema₅ {x = inj₁ x} {p} = refl
lema₅ {x = inj₂ y} {()}

--Main proof

iso₁  :  ∀{l}{A B C : Container {l}}
      →  {f : Both A B ⇒ C}
      →  uncurry (curry f) ≅ f
iso₁  =  mEq  (ext (λ { (_ , _) → refl }))
              (iext (λ { {_ , _} →
                 ext (λ _ → lema₁)}))

iso₂  :  ∀{l}{A B C : Container {l}}
      →  {g : A ⇒ (C ^ B)}
      →  curry (uncurry g) ≅ g
iso₂ {l} {A} {B} {C} {g} =
    mEq  (ext (λ _ → ext (λ _ → dSumEq refl refl (ext (λ _ → lema₂)))))
         (iext  (λ {a} →
                uncurryEq  (ext  (λ b →
                                 dcong  (Σ (Pos C (mSh (uncurry g) (a , b))))
                                        (ext (λ _ → cong  (λ x → x ≡ inj₁ tt)
                                                          lema₂))
                                        refl refl))
                           (ext  (λ _ →
                                 uncurryEq  (ext (λ _ → cong  (λ x → x ≡ inj₁ tt)
                                                              lema₂))
                                            (ext (λ _ → lema₃))))))

natural  :  ∀{l}{A A' B C  : Container {l}}
         →  (g : (Both A B) ⇒ C)
         →  (f : A' ⇒ A)
         →  curry (g ∘ (f ×ₘ id)) ≅ curry g ∘ f
natural {l} {A} {A'} {B} {C} g f =
  mEq  (ext (λ _ →
            ext (λ _ → dSumEq  refl refl
                               (ext  (λ c →
                                     lema₄ {x = mPos g c}) ))))
       (iext (λ {a'} →
             uncurryEq  (ext  (λ b →
                              dcong  (Σ (Pos C (mSh (g ∘ (f ×ₘ id)) (a' , b))))
                                     (ext  (λ c →
                                           cong  (λ x → x ≡ inj₁ tt)
                                                 (lema₄ {x = mPos g c})))
                                     refl refl))
                        (ext  (λ _ →
                              uncurryEq  (ext  (λ c →
                                               cong  (λ x → x ≡ inj₁ tt)
                                                     (lema₄ {x = mPos g c})))
                                         (ext  (λ c →
                                               dext  (λ _ →
                                                     lema₅  {f = mPos f}
                                                            {mPos g c})))))))

ContHasExponentials : ∀{l} → HasExponentials {lsuc l} 𝑪𝒐𝒏𝒕 ContHasProducts
ContHasExponentials = record
            { Exp      = _^_
            ; floor    = curry
            ; ceil     = uncurry
            ; iso₁     = iso₁
            ; iso₂     = iso₂
            ; nat      = natural
            }
