\begin{code}
module Product where
open import Container hiding (map)
open import Morphism
open import Extras
open import Data.Product as P 
open import Data.Sum as S
open import Relation.Binary.HeterogeneousEquality hiding ([_])
open Cont
open _⇒_
\end{code}

%<*Producto>
\begin{code}
Both : Cont → Cont → Cont
Both C D = (Sh C × Sh D) ◃ (λ { (c , d) → Pos C c ⊎ Pos D d })
\end{code}
%</Producto>

%<*proj1t>
\begin{code}
Π₁ : ∀{C D} → (Both C D) ⇒ C
\end{code}
%</proj1t>

%<*proj1d>
\begin{code}
Π₁ = proj₁ , inj₁
\end{code}
%</proj1d>

%<*proj2t>
\begin{code}
Π₂ : ∀{C D} → (Both C D) ⇒ D
\end{code}
%</proj2t>

%<*proj2d>
\begin{code}
Π₂ = proj₂ , inj₂
\end{code}
%</proj2d>

%<*pairt>
\begin{code}
⟨_,_⟩ : {A B C : Cont} → (C ⇒ A) → (C ⇒ B) → (C ⇒ Both A B)
\end{code}
%</pairt>

%<*paird>
\begin{code}
⟨ f , g ⟩ =  < mSh f , mSh g > , [ mPos f , mPos g ]
\end{code}
%</paird>

%<*pmap>
\begin{code}
_×ₘ_  : {A B C D : Cont}
      → (f : A ⇒ B)
      → (g : C ⇒ D)
      → Both A C ⇒ Both B D
f ×ₘ g = ⟨ f ∘ Π₁ , g ∘ Π₂ ⟩
\end{code}
%</pmap>

\begin{code}
infix 5 _×ₘ_
\end{code}

%<*pairidl>
\begin{code}
Π₁∘⟨_,_⟩≅f      :  {A B C : Cont}(f : C ⇒ A)(g : C ⇒ B) 
                →  Π₁ ∘ ⟨ f , g ⟩ ≅ f
Π₁∘⟨ f , g ⟩≅f  = refl
\end{code}
%</pairidl>

\begin{code}
Π₂∘⟨_,_⟩≅g  :  {A B C : Cont} 
            →  (f : C ⇒ A)
            →  (g : C ⇒ B) 
            →  Π₂ ∘ ⟨ f , g ⟩ ≅ g
Π₂∘⟨ f , g ⟩≅g = refl
\end{code}

%<*pairuni>
\begin{code}
pairUnique◂  :  {A B C : Cont}
             →  {f : C ⇒ A} 
             →  {g : C ⇒ B} 
             →  {h : C ⇒ Both A B}
             →  Π₁ ∘ h ≅ f 
             →  Π₂ ∘ h ≅ g
             →  h ≅ ⟨ f , g ⟩
pairUnique◂ refl refl  =
    mEq  refl
         (iext (ext (λ  {  (inj₁ _) → refl
                        ;  (inj₂ _) → refl })))
\end{code}
%</pairuni>


