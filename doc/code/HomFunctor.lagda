\begin{code}
{-# OPTIONS --type-in-type #-}
module HomFunctor where

open import Cat
open import Fun
open import CatSet
open import Relation.Binary.HeterogeneousEquality
open import Extras
open import Data.Product hiding (_×_)

open Category
\end{code}


%<*hom0>
\begin{code}
Hom₀  :  ∀{𝓒 : Category}
      →  (A : Obj 𝓒)
      →  Fun 𝓒 𝑺𝒆𝒕
Hom₀ {𝓒} A = record
    { FObj    = Hom 𝓒 A
    ; FHom    = λ f g → comp 𝓒 f g
    ; idenPr  = ext (λ _ → idl 𝓒)
    ; compPr  = ext (λ _ → sym (ass 𝓒)) }
\end{code}
%</hom0>

%<*hom1>
\begin{code}
Hom₁ :  ∀{𝓒 : Category }
     →  (B : Obj 𝓒)
     →  Fun (𝓒 ᴼᵖ) 𝑺𝒆𝒕
Hom₁ {𝓒} B = record
    { FObj    = λ A → Hom 𝓒 A B
    ; FHom    = λ f g → comp 𝓒 g f
    ; idenPr  = ext (λ _ → idl (𝓒 ᴼᵖ))
    ; compPr  = ext (λ _ → sym (ass (𝓒 ᴼᵖ)))}
\end{code}
%</hom1>

