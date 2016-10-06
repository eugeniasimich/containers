
\begin{code}

module EitherExample where
open import Container
open import Morphism
open import Sum
open import Composition
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Sum renaming ([_,_] to [_,_]𝓢et)
open import Function renaming (_∘_ to _∘̂_ ; id to idₛ)
open Cont
open _⇒_



eflip :  ∀{X Y : Cont} → Either X Y ⇒ Either Y X
eflip = [ inj₂ , inj₁ ]𝓢et , (λ { {s = inj₁ _} → idₛ ; {s = inj₂ _}  → idₛ })
\end{code}


%<*errorMes>
\begin{code}
errorMes :  ∀{C : Cont}{Str : Set}
            → Str
            → Compose cMaybe C ⇒ Either C (cK Str)
errorMes s =  (λ  {  (false  , _)     → inj₂ s
                  ;  (true   , c)     → inj₁ (c tt) }),
              (λ  {  {false  , _}  ()
                  ;  {true   , _}  x  → tt , x })
\end{code}
%</errorMes>

