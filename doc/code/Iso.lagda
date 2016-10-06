\begin{code}

module Iso  where

open import Cat
open import Relation.Binary.HeterogeneousEquality

open Category
\end{code}


%<*isInverse>
\begin{code}
record isInverse  {𝓒 : Category}{A B}
                  (f : Hom 𝓒 A B)
                  (g : Hom 𝓒 B A) : Set where
  field
    invl : comp 𝓒 g f ≅ iden 𝓒 {A}
    invr : comp 𝓒 f g ≅ iden 𝓒 {B}
\end{code}
%</isInverse>

%<*iso>
\begin{code}
record IsIsomorphism  {𝓒 : Category}{A B : Obj 𝓒}
                      (f : Hom 𝓒 A B) : Set where
  field
    inverse : Hom 𝓒 B A
    proof : isInverse {𝓒} f inverse
\end{code}
%</iso>


