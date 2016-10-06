\begin{code}
module CatExponential where

open import NaturalIsomorphism
open import HomFunctor
open import Cat

open Category
\end{code}

_ × Y →  Z
===========
 _    → Z^Y


%<*hasExponentials>
\begin{code}
record HasExponentials2 (𝓒 : Category) (pr : HasProducts 𝓒) : Set where
  field
    Exp     : Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    proof   : ∀{Y Z} → NaturalIsomorphism  {F = HomProd {p = pr} Y Z}
                                           {Hom₁ {𝓒} (Exp Z Y)}
\end{code}
%</hasExponentials>
