open import Category
open import Category.Funtor
open import Extras

module Category.Natural {o a o' a' : Level}{𝓒 : Category {o} {a}} {𝓓 : Category {o'} {a'}} (F G : Functor 𝓒 𝓓)  where

open import Relation.Binary.HeterogeneousEquality
open Category.Category
open Category.Funtor.Functor
open import Category.Isomorphism

record NaturalTransformation : Set (o ⊔ a ⊔ o' ⊔ a') where
  constructor _,_
  field
    η    :  ∀{A} → Hom 𝓓 (FObj F A) (FObj G A)
    nat  :  ∀{A B}{f : Hom 𝓒 A B}
         →  comp 𝓓 (FHom G f) η ≅ comp 𝓓 η (FHom F f)

open NaturalTransformation


record NaturalIsomorphism : Set (o ⊔ a ⊔ o' ⊔ a') where
  field
   n    : NaturalTransformation 
   n⁻¹  : ∀{A} → IsIsomorphism {o'} {a'} {𝓓} (η n {A})
