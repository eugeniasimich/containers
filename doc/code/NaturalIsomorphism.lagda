\begin{code}

module NaturalIsomorphism where

open import Cat
open import CatSet
open import Fun
open import Relation.Binary.HeterogeneousEquality
open import Extras
open import Level
open import Iso

open Category
open HasProducts
open NatT
\end{code}


%<*natiso>
\begin{code}
record NaturalIsomorphism {𝓒 𝓓}{F G : Fun 𝓒 𝓓} : Set where
  field
   n    : NatT F G
   n⁻¹  : ∀{A} → IsIsomorphism {𝓓} (η n {A})
\end{code}
%</natiso>

 
