\begin{code}
module Empty where
open import Container
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Morphism
open import Extras
open import Relation.Binary.HeterogeneousEquality hiding ([_])

open Cont
open _⇒_
\end{code}

%<*Zero>
\begin{code}
Zero : Cont
Zero = ⊥ ◃ (λ _ → ⊥)
\end{code}
%</Zero>

%<*Zerom>
\begin{code}
Zeroₘ : {C : Cont} → Zero ⇒ C
Zeroₘ = (λ ()) , (λ {})
\end{code}
%</Zerom>

%<*ZeromUnique>
\begin{code}
ZeroₘUnique  : {C : Cont}
             → {f : Zero ⇒ C}
             → Zeroₘ {C} ≅ f 
ZeroₘUnique  = mEq  (ext   (λ ()))
                    (iext  (λ {  }))
\end{code}
%</ZeromUnique>

