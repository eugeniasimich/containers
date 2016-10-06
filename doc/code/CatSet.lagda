\begin{code}
{-# OPTIONS --type-in-type #-}
module CatSet where

open import Cat
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming ([_,_] to smap ; [_,_]′ to [_,_])
open import Function renaming (_∘_ to composition ; _∘′_ to _∘_)
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Extras
\end{code}

%<*set>
\begin{code}
𝑺𝒆𝒕 : Category
𝑺𝒆𝒕 = record
           { Obj   = Set
           ; Hom   = λ R S → R → S
           ; iden  = id
           ; comp  = _∘_
           ; idl   = refl
           ; idr   = refl
           ; ass   = refl
           }
\end{code}
%</set>


\begin{code}
pairUniqueₛ  :  ∀{X Y Z : Set}{f : X → Y}{g : X → Z}
             →  ∀{h} → proj₁ ∘ h ≅ f
             →  proj₂ ∘ h ≅ g
             →  h ≅ < f , g >
pairUniqueₛ refl refl = refl
\end{code}


%<*setHasProducts>
\begin{code}
SetHasProducts : HasProducts 𝑺𝒆𝒕
SetHasProducts = record
      { Prod        = _×_
      ; projl       = proj₁
      ; projr       = proj₂
      ; pair        = <_,_>
      ; pairIdl     = λ f g → refl
      ; pairIdr     = λ f g → refl
      ; pairUnique  = pairUniqueₛ
      }
\end{code}
%</setHasProducts>

%<*setHasInitial>
\begin{code}
SetHasInitial : HasInitial 𝑺𝒆𝒕
SetHasInitial = record
  { Initial              = ⊥
  ; fromInitMor          = λ { () }
  ; isUniqueFromInitMor  = ext (λ { () })
  } 
\end{code}
%</setHasInitial>

\begin{code}
copairUniqueₛ  :  ∀{X Y Z : Set}{f : Y → X}{g : Z → X}
               →  ∀{h}
               →  h ∘ inj₁ ≅ f
               →  h ∘ inj₂ ≅ g
               →  h ≅ [ f , g ]
copairUniqueₛ refl refl = ext (λ  {  (inj₁ _) → refl
                                  ;  (inj₂ _) → refl })
\end{code}

%<*setHasTerminal>
\begin{code}
SetHasTerminal : HasTerminal 𝑺𝒆𝒕
SetHasTerminal = record
    { Terminal           = ⊤
    ; toTermMor          = λ _ → tt
    ; isUniqueToTermMor  = refl
    }
\end{code}
%</setHasTerminal>

%<*setHasCoproducts>
\begin{code}
SetHasCoproducts : HasCoproducts 𝑺𝒆𝒕
SetHasCoproducts = record
      { Coprod        = _⊎_
      ; inl           = inj₁
      ; inr           = inj₂
      ; copair        = [_,_]
      ; copairIdl     = λ f g → refl
      ; copairIdr     = λ f g → refl
      ; copairUnique  = copairUniqueₛ
      }
\end{code}
%</setHasCoproducts>

%<*setHasExponentials>
\begin{code}
SetHasExponentials : HasExponentials 𝑺𝒆𝒕 SetHasProducts
SetHasExponentials = record
    { Exp    = λ x y → y → x
    ; floor  = λ f x y → f (x , y)
    ; ceil   = λ { f (x , y) → f x y }
    ; iso₁   = refl
    ; iso₂   = refl
    ; nat    = λ f g → refl }
\end{code}
%</setHasExponentials>

