
\begin{code}
module Unit where
open import Container
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Morphism
open import Extras
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Data.Nat
open import Data.Fin
open Cont
open _⇒_
\end{code}


%<*One>
\begin{code}
One : Cont
One = ⊤ ◃ (λ _ → ⊥)
\end{code}
%</One>

%<*Onem>
\begin{code}
Oneₘ : {A : Cont} → A ⇒ One
Oneₘ = (λ _ → tt) , (λ ())
\end{code}
%</Onem>


%<*OnemUnique>
\begin{code}
OneₘUnique  : {C : Cont}
            → {f : C ⇒ One}
            → Oneₘ {C} ≅ f 
OneₘUnique = mEq refl
                 (iext (ext (λ ()))) 
\end{code}
%</OnemUnique>


\begin{code}
x : ⟦ One ⟧ ℕ
x = tt , (λ { () })

\end{code}

\begin{code}
One2 : Cont
One2 = Fin 1 ◃ (λ _ → ⊥)
\end{code}

\begin{code}
One2ₘ : {A : Cont} → A ⇒ One2
One2ₘ = (λ _ → zero) , (λ ())
\end{code}
