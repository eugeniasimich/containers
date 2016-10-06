

\begin{code}
module ExtHeter where
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Data.Product 
open import Data.Sum
\end{code}


\begin{code}
postulate dext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                 {f : ∀ a → B a}{g : ∀ a → B' a} →
                 (∀ {a a'} → a ≅ a' → f a ≅ g a') → f ≅ g
 
-- postulate extH : ∀{a b z}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}{Z : Σ A B → Set z}{Z' : Σ A' B' → Set z}
--                   {f : (a : Σ A B) → Z a}{f' : (a : Σ A' B') → Z' a} → ((a : Σ A B) → (a' : Σ A' B') → proj₁ a ≅ proj₁ a' → B ≅ B' → proj₂ a ≅ proj₂ a' → f a ≅ f' a') → f ≅ f' 

-- postulate extH2 : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
--                   {f : (a : A) → B a}{f' : (a : A') → B' a} → ((a : A) → (a' : A') → a ≅ a' → B ≅ B' → f a ≅ f' a') → f ≅ f' 

dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {f : (a : A) → B a}{f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong refl refl refl = refl

dcong₂ : ∀ {a b c} {A A' : Set a} {B : A → Set b} {B' : A' → Set b} {C : ∀ x → B x → Set c} {C' : ∀ x → B' x → Set c}
          {x : A}{y : B x}{u : A'}{v : B' u}
        (f : (x : A) (y : B x) → C x y) (f' : (x : A') (y : B' x) → C' x y) → x ≅ u → B ≅ B' → y ≅ v → C ≅ C' → f ≅ f' → f x y ≅ f' u v
dcong₂ f .f refl refl refl refl refl = refl

dSumEq : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {x : Σ A B}{y : Σ A' B'} → 
        proj₁ x ≅ proj₁ y → B ≅ B' → proj₂ x ≅ proj₂ y → x ≅ y
dSumEq refl refl refl = refl


assSum :  ∀ {a b c}
            {A : Set a}
            {B : A → Set b}
            {C : (a : A) → B a → Set c} →
            Σ A (λ a → Σ (B a) (C a)) → Σ (Σ A B) (uncurry C)
assSum (a , b , c) = (a , b) , c



move :   ∀ {a b c z}
            {A : Set a}
            {B : A → Set b}
            {C : (a : A) → B a → Set c} →
            {Z : Σ A (λ a → Σ (B a) (C a)) → Set z} →
            {ZA : Σ (Σ A B) (uncurry C) → Set z} →
            {p : ∀ a b c → Z (a , b , c) ≅ ZA ((a , b), c)} →
            (∀ abc → Z abc) → (∀ abc → ZA abc) 
move {p = p} f ((a , b) , c) = subst (λ x → x) (p a b c) (f (a , b , c))

a : ∀{a b c z}
            {A : Set a}
            {B : A → Set b}
            {C C' : (a : A) → B a → Set c}
            {Z : Σ A (λ a → Σ (B a) (C a)) → Set z} {Z' : Σ A (λ a → Σ (B a) (C' a)) → Set z}
            {f : ∀ abc → Z abc} {g : ∀ abc → Z' abc} →
            ((a : A) → (b : B a) → (c : C a b) → (c' : C' a b) →  f (a , b , c) ≅ g (a , b , c')) → 
            ((a : A) → (b : B a) → (c : C a b) → (c' : C' a b) →  move f ((a , b) , c) ≅ move g ((a , b) , c'))
a = {!!}
extHeter : ∀{a b c z}
            {A : Set a}
            {B : A → Set b}
            {C C' : (a : A) → B a → Set c}
            {Z : Σ A (λ a → Σ (B a) (C a)) → Set z} {Z' : Σ A (λ a → Σ (B a) (C' a)) → Set z}
            {f : ∀ abc → Z abc} {g : ∀ abc → Z' abc} →
            ((a : A) → (b : B a) → (c : C a b) → (c' : C' a b) →  f (a , b , c) ≅ g (a , b , c')) → f ≅ g
extHeter {f = f} {g} pr = dext (λ { {a , b , c} {a' , b' , c'} p → {!cong {f = λ x → f (x , b , c) = } (pr a b c (subst {!!} {!!} {!!}))!} })
\end{code}
