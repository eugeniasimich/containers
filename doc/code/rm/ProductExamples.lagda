\begin{code}

{-# OPTIONS --no-termination-check  #-}

module ProductExamples where
open import Container hiding (map)
open import Morphism
open import Product
open import Data.Product hiding (map)
open import Data.Sum 
open import Data.Nat
open import Data.Fin hiding (_+_ ; _<_)
open import Function renaming (id to idₛ)
open import Relation.Nullary
open Cont
\end{code}

\begin{code}
data [_] (A : Set) : Set where
  [] : [ A ]
  _∷_ : A → [ A ] → [ A ] 
\end{code}

%<*tolist>
\begin{code}
ListTo[] : ∀{A} → List A → [ A ]
ListTo[] (zero , p) = []
ListTo[] (suc s , p) =  p zero ∷ (ListTo[] (s , (λ i → p (suc i))))
\end{code}
%</tolist>

%<*splitFin>
\begin{code}
splitFin : {n₁ n₂ : ℕ}(i : Fin (n₁ + n₂)) → Fin n₁ ⊎ Fin n₂
splitFin {zero}    i        = inj₂ i
splitFin {suc n₁}  zero     = inj₁ zero
splitFin {suc n₁}  (suc i)  = map suc idₛ (splitFin i)
\end{code}
%</splitFin>


%<*appendt>
\begin{code}
append : Both cList cList ⇒ cList
\end{code}
%</appendt>

--if i < n₁ then inj₁ i else inj₂ (i - n₁)
%<*appendd>
\begin{code}
append = ( uncurry _+_ ) , splitFin
\end{code}
%</appendd>
%<*ll>
\begin{code}
ceroAdos,tresAsiete : ⟦ Both cList cList ⟧ ℕ
ceroAdos,tresAsiete = (3 , 5) , (λ  {  (inj₁ x) → toℕ x
                                    ;  (inj₂ y) → ( 3 + toℕ y ) })
\end{code}
%</ll>
%<*l>
\begin{code}
ceroAsiete : ⟦ cList ⟧ ℕ 
ceroAsiete = ⟦ append ⟧ₘ ceroAdos,tresAsiete
\end{code}
%</l>
