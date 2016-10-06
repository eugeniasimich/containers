open import Category
open import Category.Funtor
open import Extras

module Category.HomFunctors {o a : Level}(𝓒 : Category {o} {a}) where

open import Category.Examples.Sets
open import Category.Product
open import Extras
open import Relation.Binary.HeterogeneousEquality
open Category.Category
open Category.Funtor.Functor
open Category.Product.HasProducts

Hom₀ : ∀{A : Obj 𝓒} → Functor 𝓒 𝑺𝒆𝒕
Hom₀ {A} = record
    { FObj = Hom 𝓒 A
    ; FHom = λ f g → comp 𝓒 f g
    ; idenPr = ext (λ _ → idl 𝓒)
    ; compPr = ext (λ _ → sym (ass 𝓒)) }

Hom₁ : ∀{B : Obj 𝓒} → Functor (𝓒 ᴼᵖ) 𝑺𝒆𝒕
Hom₁ {B} = record
    { FObj = λ A → Hom 𝓒 A B
    ; FHom = λ f g → comp 𝓒 g f
    ; idenPr = ext (λ _ → idl (𝓒 ᴼᵖ))
    ; compPr = ext (λ _ → sym (ass (𝓒 ᴼᵖ)))}

