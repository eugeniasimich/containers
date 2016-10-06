\begin{code}
{-# OPTIONS --type-in-type #-}

module CatCont where

open import Relation.Binary.HeterogeneousEquality
open import Cat
open import Fun
open import CatSet

open import HomFunctor
open import Container
open import Product
open import Sum
open import Unit
open import Empty
open import Exponential
open import Level
open import Extras
open import Iso
open Cont
open _⇒_
\end{code}

%<*cont>
\begin{code}
𝑪𝒐𝒏𝒕 : Category
𝑪𝒐𝒏𝒕 = record
    { Obj   = Cont
    ; Hom   = _⇒_
    ; iden  = id
    ; comp  = _∘_
    ; idl   = refl
    ; idr   = refl
    ; ass   = refl }
\end{code}
%</cont>

%<*hasProducts>
\begin{code}
ContHasProducts : HasProducts 𝑪𝒐𝒏𝒕
ContHasProducts = record
            { Prod        = Both
            ; projl       = Π₁
            ; projr       = Π₂ 
            ; pair        = ⟨_,_⟩
            ; pairIdl     = λ f g → Π₁∘⟨ f , g ⟩≅f 
            ; pairIdr     = λ f g → Π₂∘⟨ f , g ⟩≅g
            ; pairUnique  = pairUnique◂ }
\end{code}
%</hasProducts>

%<*hasCoproducts>
\begin{code}            
ContHasCoproducts : HasCoproducts 𝑪𝒐𝒏𝒕
ContHasCoproducts = record
            { Coprod        = Either
            ; inl           = ι₁
            ; inr           = ι₂
            ; copair        = [_,_]
            ; copairIdl     = λ f g → [ f , g ]∘ι₁≅f
            ; copairIdr     = λ f g → [ f , g ]∘ι₂≅g
            ; copairUnique  = copairUnique◂ }
\end{code}
%</hasCoproducts>

%<*hasTerminal>
\begin{code}
ContHasTerminal : HasTerminal 𝑪𝒐𝒏𝒕
ContHasTerminal = record
            { Terminal           = One
            ; toTermMor          = Oneₘ
            ; isUniqueToTermMor  = OneₘUnique }
\end{code}
%</hasTerminal>

%<*hasInitial>
\begin{code}
ContHasInitial : HasInitial 𝑪𝒐𝒏𝒕
ContHasInitial = record
            { Initial              = Zero
            ; fromInitMor          = Zeroₘ
            ; isUniqueFromInitMor  = ZeroₘUnique }
\end{code}
%</hasInitial>


%<*hasExponentials>
\begin{code}
ContHasExponentials : HasExponentials 𝑪𝒐𝒏𝒕 ContHasProducts
ContHasExponentials = record
            { Exp      = _^_
            ; floor    = ⌊_⌋
            ; ceil     = ⌈_⌉
            ; iso₁     = iso₁
            ; iso₂     = iso₂
            ; nat      = natural }
\end{code}
%</hasExponentials>

%<*ContIsCartesianClosed>
\begin{code}
ContIsCartesianClosed : IsCartesianClosed 𝑪𝒐𝒏𝒕
ContIsCartesianClosed = record
    { hasTerminal      = ContHasTerminal
    ; hasProducts      = ContHasProducts
    ; hasExponentials  = ContHasExponentials }
\end{code}
%</ContIsCartesianClosed>

%<*extIsFunctor>
\begin{code}
⟦_⟧isFunctor : Cont → Fun 𝑺𝒆𝒕 𝑺𝒆𝒕
⟦ C ⟧isFunctor = record
    { FObj = ⟦ C ⟧
    ; FHom = map {C = C}
    ; idenPr = ext (λ _ → dSumEq refl refl refl)
    ; compPr = ext (λ _ → dSumEq refl refl refl) }
\end{code}
%</extIsFunctor>

%<*mExtIsNT>
\begin{code}
⟦_⟧ₘisNaturalTransformation  : ∀{C D}
                             → (f : C ⇒ D)
                             → NatT ⟦ C ⟧isFunctor ⟦ D ⟧isFunctor
⟦ f ⟧ₘisNaturalTransformation  = record
   { η    = ⟦ f ⟧ₘ
   ; nat  = ext (λ _ → dSumEq refl refl refl) }
\end{code}
%</mExtIsNT>
