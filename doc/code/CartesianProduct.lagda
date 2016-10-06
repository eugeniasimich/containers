
%<*times>
\begin{code}
record _×_ (X Y : Set) : Set where
  constructor _,_
  field
    proj₁ : X
    proj₂ : Y
\end{code}
%</times>

%<*reunion>
\begin{code}
<_,_> : ∀{X Y C : Set} → (C → X) → (C → Y) → (C → X × Y)
< f , g > = λ x → ( f x , g x ) 
\end{code}
%</reunion>
