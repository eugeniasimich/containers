\begin{code}
{-# OPTIONS --type-in-type #-}

module Fun where

open import Cat as C
open import Relation.Binary.HeterogeneousEquality
open import Level
open import Function
open import Extras
open Category
\end{code}

%<*fun>
\begin{code}
record Fun (𝓒 : Category)(𝓓 : Category) : Set where
  field
    FObj      :  Obj 𝓒 → Obj 𝓓
    FHom      :  ∀{A B}
              →  Hom 𝓒 A B → Hom 𝓓 (FObj A) (FObj B)
    idenPr    :  ∀{A}
              →  FHom (iden 𝓒 {A}) ≅ iden 𝓓 {FObj A}
    compPr    :  ∀{A B C}{f : Hom 𝓒 A B}{g : Hom 𝓒 B C}
              →  FHom (comp 𝓒 g f) ≅ comp 𝓓 (FHom g) (FHom f)
\end{code}
%</fun>

\begin{code}
open Fun
\end{code}

%<*nt>
\begin{code}
record NatT {𝓒 𝓓}(F G : Fun 𝓒 𝓓) : Set where
  constructor _,_
  field
    η    :  ∀{A} → Hom 𝓓 (FObj F A) (FObj G A)
    nat  :  ∀{A B}{f : Hom 𝓒 A B}
         →  comp 𝓓 (FHom G f) η ≅ comp 𝓓 η (FHom F f)
\end{code}
%</nt>

\begin{code}
open NatT
\end{code}

%<*ir>
\begin{code}
ir : {A A' : Set}{a : A}{a' : A'}{p q : a ≅ a'} → p ≅ q
ir {p = refl} {q = refl} = refl
\end{code}
%</ir>

%<*fixtypes>
\begin{code}
fixtypes : ∀{A A0}{a a' : A}{a0 a0' : A0}{p : a ≅ a'}{q : a0 ≅ a0'}
           → a ≅ a0 → a' ≅ a0' → p ≅ q
fixtypes refl refl = ir           
\end{code}
%</fixtypes>

%<*natEqt>
\begin{code}
NatT≅  :  ∀{𝓒 𝓓}{F G : Fun 𝓒 𝓓}{α β : NatT F G}
       →  (∀{X} →  η α {X} ≅ η β {X}) → α ≅ β
\end{code}
%</natEqt>

%<*natEqd>
\begin{code}
NatT≅ {𝓒 = 𝓒}{𝓓}{F}{G} p = cong₂ _,_ (iext p)
                                       (iext (iext (iext ( λ {f} →
                                           fixtypes (cong (comp 𝓓 (FHom G f)) p) (cong (λ x → comp 𝓓 x (FHom F f)) p)))))
\end{code}
%</natEqd>

%<*natIden>
\begin{code}
natIden : ∀{𝓒 𝓓}{F : Fun 𝓒 𝓓} → NatT {𝓒 = 𝓒} {𝓓} F F
natIden {𝓒 = 𝓒} {𝓓} {F} = record
    { η    = iden 𝓓
    ; nat  = trans (idr 𝓓) (sym $ idl 𝓓)}
\end{code}
%</natIden>

%<*natComp>
\begin{code}
natComp  :  ∀{𝓒 𝓓}
         →  {F G H : Fun 𝓒 𝓓}
         →  (α : NatT G H) → (β : NatT F G)
         →  NatT F H
natComp {𝓓 = 𝓓} {F} {G} {H} α β = record
    { η    =  comp 𝓓 (η α) (η β)
    ; nat  = λ    {A B f} → begin 
                     mapH f ∘̂ (η α ∘̂ η β)    ≅⟨ ass 𝓓 ⟩
                     (mapH f ∘̂ η α) ∘̂ η β    ≅⟨ cong (λ x → x ∘̂ η β) (nat α) ⟩
                     (η α ∘̂ mapG f) ∘̂ η β    ≅⟨ sym (ass 𝓓)  ⟩
                     η α ∘̂ (mapG f ∘̂ η β)    ≅⟨ cong (λ x → η α ∘̂ x) (nat β) ⟩
                     η α ∘̂ (η β ∘̂ mapF f)    ≅⟨ ass 𝓓 ⟩
                     (η α ∘̂ η β) ∘̂ mapF f    ∎ }
      where open ≅-Reasoning
            _∘̂_   = comp 𝓓
            mapH  = FHom H
            mapG  = FHom G
            mapF  = FHom F
\end{code}
%</natComp>


%<*funcat>
\begin{code}
𝑭𝒖𝒏 : Category → Category → Category
𝑭𝒖𝒏 𝓒 𝓓 = record
    {  Obj    = Fun 𝓒 𝓓
    ;  Hom    = NatT
    ;  iden   = natIden 
    ;  comp   = natComp
    ;  idl    = NatT≅ (idl 𝓓)
    ;  idr    = NatT≅ (idr 𝓓)
    ;  ass    = NatT≅ (ass 𝓓) }

\end{code}
%</funcat>
