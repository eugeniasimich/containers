\begin{code}

module MyPropositionalEquality where
open import Extras
open import Agda hiding (_≅_ ; cong; refl; sym; trans)
open import Data.Product

\end{code}

\begin{code}
infix 4 _≡_
\end{code}

%<*equiv>
\begin{code}
data _≡_ {A : Set} (x : A) : A → Set where
   refl : x ≡ x
\end{code}
%</equiv>

%<*sym>
\begin{code}
sym : ∀{A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl
\end{code}
%</sym>

%<*trans>
\begin{code}
trans : ∀{A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
\end{code}
%</trans>

%<*cong>
\begin{code}
cong : ∀{A B}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y 
cong f refl = refl
\end{code}
%</cong>

%<*subst>
\begin{code}
subst  :  ∀{A : Set}{P : A → Set}{x y}
       →  x ≡ y → P x → P y
subst {P} refl p = p
\end{code}
%</subst>

%<*scong>
\begin{code}
scong  :  ∀ {A}{B : A → Set}{x y : A}
       →  (pr : x ≡ y)
       →  (f : (x : A) → B x ) → subst pr (f x) ≡  f y 
scong refl f = refl
\end{code}
%</scong>


%<*isEquivProp>
\begin{code}
isEquivalence≡ : ∀{A} → IsEquivalence {A} _≡_ 
isEquivalence≡ = record
         { refl   = refl
         ; sym    = sym
         ; trans  = trans }
\end{code}
%</isEquivProp>

%<*zeronotone>
\begin{code}
zero≠one : zero ≡ suc zero → ⊥
zero≠one = λ { () }
\end{code}
%</zeronotone>



%<*sumasuc1>
\begin{code}
sumasuc₁ : ∀{x y : ℕ} → suma (suc x) y ≡ suc (suma x y) 
sumasuc₁ = refl
\end{code}
%</sumasuc1>

%<*sumasuc2t>
\begin{code}
sumasuc₂ : ∀{x y : ℕ} → suma x (suc y) ≡ suc (suma x y) 
\end{code}
%</sumasuc2t>

%<*sumasuc2d>
\begin{code}
sumasuc₂ {zero} = refl
sumasuc₂ {suc x} = cong suc (sumasuc₂ {x})
\end{code}
%</sumasuc2d>

