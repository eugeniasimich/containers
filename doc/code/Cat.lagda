\begin{code}
{-# OPTIONS --type-in-type #-}
module Cat where

open import Relation.Binary.HeterogeneousEquality

--open import Function
\end{code}

%<*category>
\begin{code}
record Category : Set where
  field  Obj   :  Set
         Hom   :  Obj → Obj → Set
         iden  :  ∀{A} → Hom A A
         comp  :  ∀{A B C} → Hom B C → Hom A B → Hom A C
         idl   :  ∀{A B}{f : Hom A B} → comp iden f ≅ f
         idr   :  ∀{A B}{f : Hom A B} → comp f iden ≅ f
         ass   :  ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
               →  comp h (comp g f) ≅ comp (comp h g) f
\end{code}
%</category>

\begin{code}
open Category
\end{code}

%<*op>
\begin{code}
_ᴼᵖ : Category → Category
𝓒 ᴼᵖ = record
         { Obj   = Obj 𝓒
         ; Hom   = λ A B → Hom 𝓒 B A
         ; iden  = iden 𝓒
         ; comp  = λ {A} {B} {C} f g → comp 𝓒 g f
         ; idl   = idr 𝓒
         ; idr   = idl 𝓒
         ; ass   = sym (ass 𝓒)
         }
\end{code}
%</op>

%<*hasProducts>
\begin{code}
record HasProducts (𝓒 : Category ) : Set where
  field
    Prod   : Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    projl   : ∀{X Y} → Hom 𝓒 (Prod X Y) X
    projr   : ∀{X Y} → Hom 𝓒 (Prod X Y) Y
    pair    : ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
            → Hom 𝓒 Z (Prod X Y)

  pmap  : ∀{X X' Y Y'}
        → (f : Hom 𝓒 X X')(g : Hom 𝓒 Y Y')
        → Hom 𝓒 (Prod X Y) (Prod X' Y')
  pmap f g = pair (comp 𝓒 f projl) (comp 𝓒 g projr)

  field
    pairIdl     :  ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
                   → comp 𝓒 projl (pair f g) ≅ f  
    pairIdr     :  ∀{X Y Z}(f : Hom 𝓒 Z X)(g : Hom 𝓒 Z Y)
                   → comp 𝓒 projr (pair f g) ≅ g  
    pairUnique  :  ∀{X Y Z}{f : Hom 𝓒 X Y}{g : Hom 𝓒 X Z}
                   → {h : Hom 𝓒 X (Prod Y Z)}
                   → (p₁ : comp 𝓒 projl h ≅ f)
                   → (p₂ : comp 𝓒 projr h ≅ g)
                   →  h ≅ (pair f g)
\end{code}
%</hasProducts>

%<*hasCoproducts>
\begin{code}
record HasCoproducts (𝓒 : Category) : Set where
  open Category
  field
    Coprod         :  Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    inl            :  ∀{X Y} → Hom 𝓒 X (Coprod X Y)
    inr            :  ∀{X Y} → Hom 𝓒 Y (Coprod X Y) 
    copair         :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  Hom 𝓒 (Coprod X Y) Z
    copairIdl      :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  comp 𝓒 (copair f g) inl ≅ f  
    copairIdr      :  ∀{X Y Z}(f : Hom 𝓒 X Z)(g : Hom 𝓒 Y Z)
                   →  comp 𝓒 (copair f g) inr ≅ g  
    copairUnique   :  ∀{X Y Z}{f : Hom 𝓒 X Z}{g : Hom 𝓒 Y Z}
                      {h : Hom 𝓒 (Coprod X Y) Z}
                   →  (p₁ : comp 𝓒 h inl ≅ f)
                   →  (p₂ : comp 𝓒 h inr ≅ g)
                   →  h ≅ copair f g
\end{code}
%</hasCoproducts>

%<*hasTerminal>
\begin{code}
record HasTerminal (𝓒 : Category ) : Set where
  open Category
  field
    Terminal            :  Obj 𝓒
    toTermMor           :  ∀{X} → Hom 𝓒 X Terminal 
    isUniqueToTermMor   :  ∀{X}{f : Hom 𝓒 X Terminal}
                        →  toTermMor {X} ≅ f
\end{code}
%</hasTerminal>

%<*hasInitial>
\begin{code}
record HasInitial (𝓒 : Category) : Set where
  open Category
  field
    Initial               :  Obj 𝓒
    fromInitMor           :  ∀{X} → Hom 𝓒 Initial X 
    isUniqueFromInitMor   :  ∀{X}{f : Hom 𝓒 Initial X}
                          →  fromInitMor {X} ≅ f
\end{code}
%</hasInitial>


\begin{code}
open Category
open HasProducts
\end{code}

%<*hasExponentials>
\begin{code}
record HasExponentials (𝓒 : Category) (pr : HasProducts 𝓒) : Set where
  field
    Exp     :  Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    floor   :  ∀{X Y Z}
            →  Hom 𝓒 (Prod pr X Y) Z
            →  Hom 𝓒 X (Exp Z Y)
    ceil    :  ∀{X Y Z}
            →  Hom 𝓒 X (Exp Z Y)
            →  Hom 𝓒 (Prod pr  X Y) Z
    iso₁    :  ∀{X Y Z}{f : Hom 𝓒 (Prod pr X Y) Z}
            →  ceil (floor f) ≅ f
    iso₂    :  ∀{X Y Z}{f : Hom 𝓒 X (Exp Z Y)}
            →  floor (ceil f) ≅ f
    nat     :  ∀{X X' Y Z : Obj 𝓒}
            →  (g : Hom 𝓒 (Prod pr X Y) Z)
            →  (f : Hom 𝓒 X' X)
            →  floor (comp 𝓒 g (pmap pr f (iden 𝓒))) ≅ comp 𝓒 (floor g) f
\end{code}
%</hasExponentials>

ojo: cosas que le saqué a la definición de exponencial porque no hacía falta...
  emap  :  ∀{X Y Z Z'}(f : Hom 𝓒 Z Z')(h : Hom 𝓒 X (Exp Z Y))
        →  Hom 𝓒 X (Exp Z' Y) 
  emap f h = floor (comp 𝓒 f (ceil h))

    nat₂    :  ∀{X Y Z Z' : Obj 𝓒}
            →  (g : Hom 𝓒 (Prod pr X Y) Z)
            →  (f : Hom 𝓒 Z Z')
            →  emap f (floor g) ≅ floor (comp 𝓒 f g)              

%<*IsCartesianClosed>
\begin{code}
record IsCartesianClosed (𝓒 : Category) : Set where
  field
    hasTerminal      :  HasTerminal 𝓒
    hasProducts      :  HasProducts 𝓒
    hasExponentials  :  HasExponentials 𝓒 hasProducts
\end{code}
%</IsCartesianClosed>
