\begin{code}
module EExp where
open import Container hiding (map)
open import Data.Product hiding (map)
open import Data.Sum  
open import Data.Unit
open import Function renaming (id to idₛ ; _∘_ to _∘ₛ_) 
open import Morphism
open import Extras
open import Product
open import Relation.Binary.HeterogeneousEquality hiding ([_];inspect)
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

open Cont
open _⇒_

\end{code}


\begin{code}
_^_ : Cont → Cont → Cont
D ^ C = ((s : Sh C) → Σ[ t ∈ Sh D ] (Pos D t → ⊤ ⊎ Pos C s))
       ◃ (λ f → Σ[ s ∈ Sh C ] (Σ[ q ∈ Pos D (proj₁ (f s)) ] ((proj₂ (f s)) q ≡ inj₁ tt)))




eval : ∀{A B} → Both (B ^ A) A ⇒ B
eval = (λ x → proj₁ $ proj₁ x (proj₂ x)) ,
       (λ { {ba , a} x → pos {ba = ba} {a = a} {x}})
     where pos : ∀ {A B}
                 {ba : Sh (B ^ A)}
                 {a : Sh A} →
                 ∀{x : Pos B (proj₁ (ba a))} →
                 Σ (Sh A)
                   (λ s₁ →
                     Σ (Pos B (proj₁ (ba s₁))) (λ q → proj₂ (ba s₁) q ≡ inj₁ tt))
                   ⊎ Pos A a
           pos {ba = ba} {a} {x} with proj₂ (ba a) x | inspect (proj₂ (ba a)) x
           pos {ba = ba} {a} {x} | inj₁ tt | [[ eq ]] = inj₁ (a , x , eq)
           pos {ba = ba} {a} {x} | inj₂ y  | p = inj₂ y


flatLeft : ∀ {A B : Set} → A ⊎ B → ⊤ ⊎ B
flatLeft = map (λ _ → tt) idₛ 

fromInj₁ : ∀ {A B : Set} → (b : A ⊎ B) → (flatLeft b ≡ inj₁ tt) →  A
fromInj₁ (inj₁ x) pr = x
fromInj₁ (inj₂ y) ()

insLeft : ∀{A B : Set} → (b : ⊤ ⊎ B) → (b ≡ inj₁ tt → A) → A ⊎ B
insLeft (inj₁ _) pr = inj₁ (pr refl)
insLeft (inj₂ y) pr = inj₂ y

--curry
Λ_ : ∀{A B C : Cont} → (Both A B) ⇒ C → A ⇒ (C ^ B)
Λ f  = (λ a b → mSh f (a , b) , flatLeft ∘ₛ (mPos f) ),
        (λ { {a} (b , c , r) → fromInj₁ (mPos f {a , b} c) r })

infix 6 Λ_
--upwards
-- ⌈_⌉ : ∀{A B C : Cont} → A ⇒ (C ^ B) → Both A B ⇒ C
-- ⌈ f ⌉ = proj₁ ∘ₛ uncurry (mSh f) , 
--         (λ { {a , b} c → insLeft (proj₂ (mSh f a b) c) (λ pr → (mPos f {a} (b , c , pr ))) }) 


-- ^map : {A B C C' : Cont} → (f : C ⇒ C') → (h : A ⇒ C ^ B) → A ⇒ C' ^ B
-- ^map f h = ⌊ f ∘ ⌈ h ⌉ ⌋

-- aa :  ∀ {A B C} {g : Both A B ⇒ C}
--          {s : Sh (Both A B)}
--          {c : Pos C (mSh g s)} →
--          mPos g {s} c ≅ ((λ {x} → mPos (Λ g ×ₘ (id {B}))) ∘ₛ mPos (eval {B} {C})) c
-- aa {g = g} {s} {c} with mPos g c
-- ... | j = ?
--with mPos g {s} c
--... | j = ?


--[
 --       (λ x →
 --          inj₁ (fromInj₁ (mPos g (proj₁ (proj₂ x))) (proj₂ (proj₂ x))))
 --       , inj₂ ]
 --       (_.pos {B} {C} {B} {C}
 --        {λ b →
 --           mSh g (proj₁ s₁ , b) ,
 --           (λ x → [ (λ x₁ → inj₁ tt) , inj₂ ] (mPos g x))}
 --        {proj₂ s₁} {c}
 --        | [ (λ x → inj₁ tt) , inj₂ ] (mPos g c) | [[ refl ]])


Λcommutes : ∀ {A B C}
          → (g : Both A B ⇒ C)
          → g ≅  eval ∘ (Λ g ×ₘ (id {B}))
Λcommutes g = mEq
                  (ext (λ a → refl))
                  (iext (λ { {a , b} → ext (λ c → {!!}) }))




Λunique : ∀ {A B C}
          → (g : Both A B ⇒ C)
          → (h : Both A B ⇒ Both (C ^ B) B)
          → eval ∘ h ≅ g
          → h ≅  Λ g ×ₘ (id {B}) 
Λunique _ h refl =
    mEq  (ext (λ { (a , b) →
           dSumEq (ext (λ b₁ → dSumEq {!!}
                                refl
                                {!!}))
               refl
               {!!} }))
         (iext (λ { {a , b} → {!case proj₂ (ba a) x!} }))
\end{code}


mSh : ∀ {A B C}
        {h
         : (Σ (Sh A) (λ x → Sh B) ◃
            (λ cd → Pos A (proj₁ cd) ⊎ Pos B (proj₂ cd)))
           ⇒
           (Σ ((s₁ : Sh B) → Σ (Sh C) (λ t → Pos C t → ⊤ ⊎ Pos B s₁))
            (λ x → Sh B)
            ◃
            (λ cd →
               Σ (Sh B)
               (λ s₁ →
                  Σ (Pos C (proj₁ (proj₁ cd s₁)))
                  (λ q → proj₂ (proj₁ cd s₁) q ≡ inj₁ tt))
               ⊎ Pos B (proj₂ cd)))}
        {a : Sh A} {b : Sh B} →
      mSh h (a , b) ≅
      ((λ b₁ →
          proj₁ (proj₁ (mSh h (a , b₁)) (proj₂ (mSh h (a , b₁)))) ,
          (λ x →
             [ (λ x₁ → inj₁ tt) , inj₂ ]
             (mPos h
              (_.pos {B} {C} {B} {C} {proj₁ (mSh h (a , b₁))}
               {proj₂ (mSh h (a , b₁))} {x}
               | proj₂ (proj₁ (mSh h (a , b₁)) (proj₂ (mSh h (a , b₁)))) x
               | [[ refl ]]))))
       , b)
