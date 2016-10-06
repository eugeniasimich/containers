\begin{code}
module Extras where
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Data.Product 
open import Data.Sum
\end{code}

%<*ext>
\begin{code}
postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}
                    {f : ∀ a → B a}{g : ∀ a → B' a} → 
                    (∀ a → f a ≅ g a) → f ≅ g
\end{code}
%</ext>

%<*iext>
\begin{code}
postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}
                    {f : ∀ {a} → B a}{g : ∀ {a} → B' a} → 
                    (∀ {a} → f {a} ≅ g {a}) → (λ {a} → f {a}) ≅ (λ {a} → g {a})
\end{code}
%</iext>

%<*dext>
\begin{code}
postulate dext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                 {f : ∀ a → B a}{g : ∀ a → B' a} →
                 (∀ {a a'} → a ≅ a' → f a ≅ g a') → f ≅ g
\end{code}
%</dext>


%<*dcong>
\begin{code}
dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        (f : (a : A) → B a){f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong f refl refl refl = refl
\end{code}
%</dcong>

%<*dSumEq>
\begin{code}
dSumEq : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {x : Σ A B}{y : Σ A' B'} → 
        proj₁ x ≅ proj₁ y → B ≅ B' → proj₂ x ≅ proj₂ y → x ≅ y
dSumEq refl refl refl = refl
\end{code}
%</dSumEq>
