\begin{code}
module Exponential where
open import Container hiding (map)
open import Data.Product hiding (map) renaming (curry to curryₛ ; uncurry to uncurryₛ)
open import Data.Sum --renaming (map to map₊)
open import Data.Unit
open import Function renaming (id to idₛ ; _∘_ to _∘ₛ_) 
open import Morphism
open import Extras
open import Product 
open import Relation.Binary.HeterogeneousEquality hiding ([_] ; inspect)
open import Relation.Binary.PropositionalEquality hiding (cong)--using (_≡_; refl)

open Cont
open _⇒_ 

\end{code}

%<*exp>
\begin{code}
_^_ : Cont → Cont → Cont
C ^ B  =  ((b : Sh B) → Σ[ c ∈ Sh C ] (Pos C c → ⊤ ⊎ Pos B b))
       ◃
          (λ f →  Σ[ b ∈ Sh B ] (Σ[ q ∈ Pos C (proj₁ (f b))]
                  (proj₂ (f b) q ≡ inj₁ tt)))
\end{code}
%</exp>

-- F × G ⇒ H
-- ----------
--  F ⇒ H^G

--map (λ _ → tt) idₛ 
%<*eraseLeft>
\begin{code}
eraseLeft : {A B : Set} → A ⊎ B → ⊤ ⊎ B
eraseLeft (inj₁ x) = inj₁ tt
eraseLeft (inj₂ y) = inj₂ y
\end{code}
%</eraseLeft>

%<*fromInj1>
\begin{code}
fromInj₁ : {A B : Set} → (b : A ⊎ B) → (eraseLeft b ≡ inj₁ tt) →  A
fromInj₁ (inj₁ x) pr = x
fromInj₁ (inj₂ y) ()
\end{code}
%</fromInj1>

%<*insLeft>
\begin{code}
insLeft : {A B : Set} → (b : ⊤ ⊎ B) → (b ≡ inj₁ tt → A) → A ⊎ B
insLeft (inj₁ _)  pr = inj₁ (pr refl)
insLeft (inj₂ y)  pr = inj₂ y
\end{code}
%</insLeft>

--downwards
%<*floor>
\begin{code}
curry : {A B C : Cont} → (Both A B ⇒ C) → (A ⇒ C ^ B)
curry f = (λ a b → mSh f (a , b) , eraseLeft ∘ₛ (mPos f) ), 
        (λ { {a} (b , c , r) → fromInj₁ (mPos f {a , b} c) r })
\end{code}
%</floor>

--upwards
%<*ceil>
\begin{code}
uncurry : {A B C : Cont} → (A ⇒ C ^ B) → (Both A B ⇒ C)
uncurry f  = proj₁ ∘ₛ uncurryₛ (mSh f) , 
        (λ { {a , b} c → insLeft  (proj₂ (mSh f a b) c)
                                  (λ pr → (mPos f {a} (b , c , pr))) }) 
\end{code}
%</ceil>

%<*emap>
\begin{code}
emap : {A B C C' : Cont} → (f : C ⇒ C') → (h : A ⇒ C ^ B) → A ⇒ C' ^ B
emap f h = curry (f ∘ uncurry h)
\end{code}
%</emap>

%<*emap>
\begin{code}
eval : {B C : Cont} → Both (C ^ B) B ⇒ C
eval = (λ { (bc , b) → proj₁ (bc b) }) , (λ { {bc , b} q → choose b bc q })
  where  choose : ∀{C B} → (b : Sh B) → (bc : (b : Sh B) → Σ (Sh C) (λ c → Pos C c → ⊤ ⊎ Pos B b)) → (q  : Pos C (proj₁ (bc b))) → Pos (Both (C ^ B) B) (bc , b)
         choose b bc q with proj₂ (bc b) q | inspect (proj₂ (bc b)) q
         choose b bc q | inj₁ tt | [ eq ] = inj₁ (b , (q , eq))
         choose b bc q | inj₂ y  | [ eq ] = inj₂ y
\end{code}
%</emap>


--now the proof of:
-- curry . uncurry = id = uncurry . curry

--Auxiliary proofs

%<*aux1>
\begin{code}
lema₁ :  {A B : Set}
      →  {a : A ⊎ B} 
      →  insLeft (eraseLeft a) (fromInj₁ a) ≅ a
lema₁ {a = inj₁ x} = refl
lema₁ {a = inj₂ y} = refl
\end{code}
%</aux1>

%<*aux2>
\begin{code}
lema₂  :  {A B : Set}
                     →  {a : ⊤ ⊎ B}
                     →  {f : a ≡ inj₁ tt → A}
                     →  eraseLeft (insLeft a f) ≅ a
lema₂ {a = inj₁ x} = refl
lema₂ {a = inj₂ y} = refl
\end{code}
%</aux2>

%<*aux3>
\begin{code}
lema₃  :  {A B : Set}
                     →  {b : ⊤ ⊎ B}
                     →  {f : b ≡ inj₁ tt → A }
                     → fromInj₁ (insLeft b f) ≅ f
lema₃ {b = inj₁ tt}  = dext (λ  { {a = refl} {refl} _
                                              → refl })
lema₃ {b = inj₂ _}   = ext (λ { () })
\end{code}
%</aux3>

%<*uncurryEq>
\begin{code}
uncurryEq  :  ∀{A : Set} {B B' : A → Set} {C : Set }
           →  {f : (p : Σ A B) → C } {g : (p : Σ A B') → C}
           →  B ≅ B' → curryₛ f ≅ curryₛ g → f ≅ g
uncurryEq refl p = dcong uncurryₛ p refl refl 
\end{code}
%</uncurryEq>

%<*aux4>
\begin{code}
lema₄  :  {A B C : Set}{f : A → C}{a : A ⊎ B}
       →  eraseLeft (map f idₛ a) ≅ eraseLeft a 
lema₄ {a = inj₁ x} = refl
lema₄ {a = inj₂ y} = refl
\end{code}
%</aux4>

%<*aux5>
\begin{code}
lema₅ :
      ∀{A B C : Set}{f : A → C}{a : A ⊎ B}{p2}
   →  {p1 : eraseLeft (map f idₛ a) ≡ inj₁ tt}
   →  (fromInj₁ ∘ₛ map f idₛ) a p1 ≅ f (fromInj₁ a p2)
lema₅ {a = inj₁ x} {p} = refl
lema₅ {a = inj₂ y} {()}
\end{code}
%</aux5>

--Main proof
%<*iso1>
\begin{code} 
iso₁  :  {A B C : Cont}
      →  {f : Both A B ⇒ C}
      →  uncurry (curry f) ≅ f
iso₁  =  mEq  (ext (λ { (_ , _) → refl }))
              (iext (λ { {_ , _} →
                 ext (λ _ → lema₁)}))
\end{code}
%</iso1>

%<*iso2>
\begin{code}
iso₂  :  {A B C : Cont}
      →  {g : A ⇒ (C ^ B)}
      →  curry (uncurry g)  ≅ g
iso₂ {A} {B} {C} {g} =
    mEq  (ext  (λ _ → ext (λ _ → dSumEq  refl refl
                                        (ext (λ _ → lema₂)))))
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
\end{code}
%</iso2>

%<*natural>
\begin{code}
natural  :  {A A' B C  : Cont}
         →  (g : (Both A B) ⇒ C)
         →  (f : A' ⇒ A)
         →  curry (g ∘ (f ×ₘ id)) ≅ curry g ∘ f
natural {A} {A'} {B} {C} g f =
  mEq  (ext (λ _ →
            ext (λ _ → dSumEq  refl refl
                               (ext  (λ c →
                                     lema₄ {a = mPos g c}) ))))
       (iext (λ {a'} →
             uncurryEq  (ext  (λ b →
                              dcong  (Σ (Pos C (mSh (g ∘ (f ×ₘ id)) (a' , b))))
                                     (ext  (λ c →
                                           cong  (λ x → x ≡ inj₁ tt)
                                                 (lema₄ {a = mPos g c})))
                                     refl refl))
                        (ext  (λ _ →
                              uncurryEq  (ext  (λ c →
                                               cong  (λ x → x ≡ inj₁ tt)
                                                     (lema₄ {a = mPos g c})))
                                         (ext  (λ c →
                                               dext  (λ _ →
                                                     lema₅  {f = mPos f}
                                                            {mPos g c})))))))
\end{code}
%</natural>

