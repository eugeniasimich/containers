\begin{code}
{-# OPTIONS --type-in-type #-}
module ListFun where

open import Cat
open import Fun
open import CatSet
open import Relation.Binary.HeterogeneousEquality
open import Extras

open Category
\end{code}

%<*list>
\begin{code}
data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A
\end{code}
%</list>

%<*map>
\begin{code}
map : ∀{A B} → (A → B) → List A → List B
map f nil = nil
map f (cons x l) = cons (f x) (map f l)
\end{code}
%</map>

\begin{code}
idenPrList : ∀{A} → (l : List A) → map (iden 𝑺𝒆𝒕) l  ≅ iden 𝑺𝒆𝒕 l
idenPrList nil = refl
idenPrList (cons x l) = cong (cons x) (idenPrList l)

compPrList : ∀{A B C}{g : A → B}{f : B → C} → (l : List A) → map (comp 𝑺𝒆𝒕 f g) l ≅ comp 𝑺𝒆𝒕 (map f) (map g) l
compPrList nil = refl
compPrList {g = g} {f} (cons x l) = cong (cons (comp 𝑺𝒆𝒕 f g x)) (compPrList l)
\end{code}

%<*listFun>
\begin{code}
ListFun : Fun 𝑺𝒆𝒕 𝑺𝒆𝒕 
ListFun = record
    { FObj    = List
    ; FHom    = map
    ; idenPr  = ext idenPrList
    ; compPr  = ext compPrList }
\end{code}
%</listFun>

%<*snoc>
\begin{code}
snoc : ∀{A} → A →  List A → List A
snoc a nil = cons a nil
snoc a (cons x l) = cons x (snoc a l)
\end{code}
%</snoc>

%<*reverse>
\begin{code}
reverse : ∀{A} → List A → List A
reverse nil = nil
reverse (cons x l) = snoc x (reverse l)
\end{code}
%</reverse>

\begin{code}
open Fun.Fun

snocmap : ∀{A B}{x}{l : List A}{f : A → B} → map f (snoc x l) ≅ snoc (f x) (map f l)
snocmap {l = nil} = λ {f} → refl
snocmap {l = cons x l} {f} = cong (cons (f x)) (snocmap {l = l} {f})

reverseNat : ∀{A B}{f : A → B}→ (l : List A) → comp 𝑺𝒆𝒕 (FHom ListFun f) reverse l ≅ comp 𝑺𝒆𝒕 reverse (FHom ListFun f) l
reverseNat nil = refl
reverseNat {f = f} (cons x l) = trans (snocmap {x = x} {l = reverse l}) (cong (snoc (f x)) (reverseNat {f = f} l))
\end{code}


%<*reverseNatT>
\begin{code}
reverseNatT : NatT ListFun ListFun
reverseNatT = record
    { η    = reverse
    ; nat  = ext reverseNat} 
\end{code}
%</reverseNatT>
