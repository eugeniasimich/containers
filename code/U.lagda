\begin{code}
module U where
\end{code}

\begin{code}
data _×_ (X Y : Set) : Set where
  _,_ : X → Y → X × Y
\end{code}

\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat → Nat
\end{code}

\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool
\end{code}

%<*U>
\begin{code}
data U : Set where
  nat   : U
  bool  : U
  pair  : U → U → U
\end{code}
%</U>

%<*Uext>
\begin{code}
⟦_⟧ : U → Set
⟦ nat ⟧          = Nat
⟦ bool ⟧         = Bool
⟦ pair t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
\end{code}
%</Uext>
