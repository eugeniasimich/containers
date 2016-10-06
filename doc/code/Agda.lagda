
\begin{code}

module Agda where
\end{code}

%<*bool>
\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool
\end{code}
%</bool>

%<*bot>
\begin{code}
data ⊥ : Set where
\end{code}
%</bot>

%<*top>
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
%</top>


%<*not>
\begin{code}
not : Bool → Bool
not true   = false
not false  = true
\end{code}
%</not>

%<*and>
\begin{code}
and : Bool → Bool → Bool
and = λ  { true   y  → y
         ; false  _  → false }
\end{code}
%</and>

%<*xor>
\begin{code}
xor : Bool → Bool → Bool
xor = λ  { true   true   → false
         ; false  false  → false
         ; _      _      → true}
\end{code}
%</xor>

%<*idBool>
\begin{code}
idBool : Bool → Bool
idBool x = x
\end{code}
%</idBool>

%<*id1>
\begin{code}
id₁ : (X : Set) → X → X
id₁ _ x = x
\end{code}
%</id1>

%<*id>
\begin{code}
id : {X : Set} → X → X
id x = x
\end{code}
%</id>

%<*atrue>
\begin{code}
atrue : Bool → Bool
atrue _ = true
\end{code}
%</atrue>

%<*empty1>
\begin{code}
empty₁ : (X : Set) → ⊥ → X
empty₁ X ()
\end{code}
%</empty1>

%<*empty>
\begin{code}
empty : {X : Set} → ⊥ → X
empty ()
\end{code}
%</empty>

%<*emptyToBool>
\begin{code}
emptyToBool : ⊥ → Bool
emptyToBool ()
\end{code}
%</emptyToBool>




%<*times>
\begin{code}
data _×_ (X Y : Set) : Set where
  _,_ : X → Y → X × Y
\end{code}
%</times>


%<*proj1>
\begin{code}
proj₁ : ∀{X Y} → X × Y → X
proj₁ (x , y) = x
\end{code}
%</proj1>

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>

%<*suma>
\begin{code}
suma : ℕ → ℕ → ℕ
suma  zero     y = y
suma  (suc x)  y = suc (suma x y)
\end{code}
%</suma>

%<*sumaInfija>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero     + y  = y
(suc x)  + y  = suc (x + y)
\end{code}
%</sumaInfija>

%<*Vec>
\begin{code}
data Vec (A : Set) : ℕ → Set where
   nil   : Vec A zero
   cons  : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%</Vec>

%<*append>
\begin{code}
append : ∀{A n m} → Vec A n → Vec A m → Vec A (suma n m)
append nil u = u
append (cons x v) u = cons x (append v u)
\end{code}
%</append>

%<*neg>
\begin{code}
¬ : Set → Set
¬ A = A → ⊥
\end{code}
%</neg>

%<*isEquiv>
\begin{code}
record IsEquivalence {A : Set} (_≈_ :  A → A → Set) : Set where
  field
    refl  : ∀{x} → x ≈ x  
    sym   : ∀{x y} → x ≈ y → y ≈ x 
    trans : ∀{x y z} → x ≈ y → y ≈ z → x ≈ z
\end{code}
%</isEquiv>

%<*equivH>
\begin{code}
data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
   refl : x ≅ x
\end{code}
%</equivH>

\begin{code}
infix  4 _≅_
\end{code}

%<*cong>
\begin{code}
cong  :  ∀{A : Set}{B : A → Set}{x y}
      →  (f : (x : A) → B x) → x ≅ y → f x ≅ f y 
cong f refl = refl
\end{code}
%</cong>

%<*sym>
\begin{code}
sym : ∀{A B}{x : A}{y : B} →  x ≅ y → y ≅ x 
sym refl = refl
\end{code}
%</sym>

%<*trans>
\begin{code}
trans : ∀{A B C}{x : A}{y : B}{z : C} → x ≅ y → y ≅ z → x ≅ z 
trans refl refl = refl
\end{code}
%</trans>


%<*isEquivHeter>
\begin{code}
isEquivalence≅ : ∀{A} → IsEquivalence {A} (λ x y → x ≅ y) 
isEquivalence≅ = record
         { refl   = refl
         ; sym    = sym
         ; trans  = trans }
\end{code}
%</isEquivHeter>

%<*sumaEquivExt>
\begin{code}
sumaEquivExt : ∀{x y} → suma x y ≅ x + y
sumaEquivExt {zero}   = refl
sumaEquivExt {suc x}  = cong suc (sumaEquivExt {x})
\end{code}
%</sumaEquivExt>

\begin{code}
postulate ext  :  {A : Set}{B B' : A → Set}
                  {f : ∀ a → B a}{g : ∀ a → B' a}
               →  (∀ a → f a ≅ g a)
               →  f ≅ g
\end{code}


%<*sumaEquiv>
\begin{code}
sumaEquiv : suma ≅ _+_ 
sumaEquiv = ext (λ x → ext (λ y → sumaEquivExt {x} {y}))
\end{code}
%</sumaEquiv>
