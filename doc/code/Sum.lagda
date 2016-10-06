\begin{code}
module Sum where
open import Container
open import Morphism
open import Extras
open import Data.Product
open import Data.Sum renaming ([_,_] to [_,_]ₛ)
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open import Function renaming (id to idₛ ; _∘_ to _∘_ₛ)
open Cont
open _⇒_
\end{code}

%<*either>
\begin{code}
Either : Cont → Cont → Cont
Either C D = (Sh C ⊎ Sh D) ◃ [ Pos C , Pos D ]ₛ
\end{code}
%</either>

%<*inj1>
\begin{code}
ι₁ : ∀{C D} → C ⇒ Either C D
ι₁ = inj₁ , idₛ
\end{code}
%</inj1>

\begin{code}
ι₂ : ∀{C D} → D ⇒ Either C D
ι₂ = inj₂ , idₛ
\end{code}

%<*coreunion>
\begin{code}
[_,_] :  ∀ {A B C} → (A ⇒ C) → (B ⇒ C) → (Either A B ⇒ C)
[ f , g ] = [ mSh f , mSh g ]ₛ  ,  (λ {  {inj₁ x}  →  mPos f {x}
                                ;        {inj₂ y}  →  mPos g {y} })
\end{code}
%</coreunion>

--Proof that Either is sum type:
%<*copairIdl>
\begin{code}
[_,_]∘ι₁≅f  : ∀ {A B C}
            → (f : A ⇒ C)
            → (g : B ⇒ C)
            → [ f , g ] ∘ ι₁ ≅ f
[ f , g ]∘ι₁≅f  = refl
\end{code}
%</copairIdl>

%<*copairIdr>
\begin{code}
[_,_]∘ι₂≅g : ∀ {A B C}
           → (f : A ⇒ C)
           → (g : B ⇒ C)
           → [ f , g ] ∘ ι₂ ≅ g
[ f , g ]∘ι₂≅g = refl
\end{code}
%</copairIdr>

%<*copairUnique>
\begin{code}
copairUnique◂  : {A B C : Cont}
               → {f : A ⇒ C}
               → {g : B ⇒ C}
               → {h : Either A B ⇒ C}
               → h ∘ ι₁  ≅ f
               → h ∘ ι₂  ≅ g
               → h ≅ [ f , g ]
copairUnique◂ refl refl =
    mEq  (ext   ( λ  {  (inj₁ _) → refl
                     ;  (inj₂ _) → refl }))
         (iext  ( λ  {  {inj₁ _} → ext (λ _ → refl)
                     ;  {inj₂ _} → refl }))
\end{code}
%</copairUnique>
