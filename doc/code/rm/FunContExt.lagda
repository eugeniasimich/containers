\begin{code}
{-# OPTIONS --type-in-type #-}
module FunContExt where

open import Cat as C
open import Fun
open import CatSet
open import Container
open import Relation.Binary.HeterogeneousEquality
open import Level
open import Function
open import Extras
open Category
open Fun.Fun


⟦_⟧isFunctor : Cont → Fun 𝑺𝒆𝒕 𝑺𝒆𝒕
⟦ C ⟧isFunctor = record
    { FObj = ⟦ C ⟧
    ; FHom = map {C = C}
    ; idenPr = ext (λ _ → dSumEq refl refl refl)
    ; compPr = ext (λ _ → dSumEq refl refl refl)
    }

\end{code}
