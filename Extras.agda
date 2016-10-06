module Extras where

open import Function public renaming (id to idₛ; _∘_ to _∘ₛ_) public
open import Relation.Binary.HeterogeneousEquality public hiding ([_])
open ≅-Reasoning public
open import Data.Product public renaming (curry to curryₛ; uncurry to uncurryₛ)
open import Level public renaming (suc to lsuc; zero to lzero) hiding (lift)
open import Data.Unit public using (⊤; tt)
open import Data.Empty public using (⊥)
open import Data.Sum public renaming (map to mapₛ; [_,_] to [_,_]ₛ)


postulate ext : ∀  {a b}{A : Set a}{B B' : A → Set b}
                   {f : ∀ a → B a}{g : ∀ a → B' a} → 
                   (∀ a → f a ≅ g a) → f ≅ g

postulate iext : ∀  {a b}{A : Set a}{B B' : A → Set b}
                    {f : ∀ {a} → B a}{g : ∀ {a} → B' a} → 
                    (∀ {a} → f {a} ≅ g {a}) → (λ {a} → f {a}) ≅ (λ {a} → g {a})

postulate dext : ∀  {a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                    {f : ∀ a → B a}{g : ∀ a → B' a} →
                    (∀ {a a'} → a ≅ a' → f a ≅ g a') → f ≅ g

dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        (f : (a : A) → B a){f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong f refl refl refl = refl

dSumEq : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {x : Σ A B}{y : Σ A' B'} → 
        proj₁ x ≅ proj₁ y → B ≅ B' → proj₂ x ≅ proj₂ y → x ≅ y
dSumEq refl refl refl = refl


ir : ∀{a}{A A' : Set a}{x : A}{x' : A'}{p q : x ≅ x'} → p ≅ q
ir {p = refl} {q = refl} = refl

fixtypes : ∀{a}{A A0 : Set a}{x x' : A}{y y' : A0}{p : x ≅ x'}{q : y ≅ y'}
           → x ≅ y → x' ≅ y' → p ≅ q
fixtypes refl refl = ir     
