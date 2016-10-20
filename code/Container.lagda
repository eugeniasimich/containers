\begin{code}
module Container where

open import Data.Bool
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin hiding (_+_)
open import Data.Unit renaming (⊤ to Unit)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty renaming (⊥ to ∅)
open import Function --renaming (id to idₛ)
open import Relation.Binary.HeterogeneousEquality hiding ([_])
\end{code}

%<*cont>
\begin{code}
record Cont : Set₁ where
  constructor _◃_
  field
    Sh  : Set 
    Pos : Sh → Set 
\end{code}
%</cont>

\begin{code}
open Cont
\end{code}

%<*ext>
\begin{code}
⟦_⟧ : Cont → Set → Set 
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)
\end{code}
%</ext>


%<*map>
\begin{code}
map : ∀{X Y C} → (f : X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f (s , p) = s , (f ∘ p)
\end{code}
%</map>



%<*clist>
\begin{code}
cList : Cont
cList = Nat ◃ (λ n → Fin n)
\end{code}
%</clist>

%<*listconstructors>
\begin{code}
nil : ∀{X} → ⟦ cList ⟧ X
nil = zero , (λ ())

cons : ∀{X} → X → ⟦ cList ⟧ X → ⟦ cList ⟧ X
cons x (n , f) = ( suc n , (λ  { zero     → x
                               ; (suc i)  → f i }) )
\end{code}
%</listconstructors>

%<*cId>
\begin{code}
cId : Cont
cId = Unit ◃ (λ _ → Unit)
\end{code}
%</cId>

%<*Id>
\begin{code}
identity : ∀{X} → X → ⟦ cId ⟧ X
identity x = tt , (λ _ → x)
\end{code}
%</Id>

%<*cK>
\begin{code}
cK : Set → Cont
cK A = A ◃ (λ _ → ∅)
\end{code}
%</cK>

%<*K>
\begin{code}
K : Set → Set → Set
K A = ⟦ cK A ⟧
\end{code}
%</K>

%<*dos>
\begin{code}
dos : ⟦ cK Nat ⟧ ∅
dos = 2 , (λ { () })
\end{code}
%</dos>

%<*cmaybe>
\begin{code}
cMaybe : Cont
cMaybe = Bool ◃ (λ  { false  → ∅
                    ; true   → Unit }) 
\end{code}
%</cmaybe>

%<*maybe>
\begin{code}
nothing : ∀{X} → ⟦ cMaybe ⟧ X
nothing = false , (λ { () })

just : ∀{X} → X → ⟦ cMaybe ⟧ X
just x = true , (λ { tt → x })
\end{code}
%</maybe>

%<*cstream>
\begin{code}
cStream : Cont
cStream = Unit ◃ (λ {_ → Nat})
\end{code}
%</cstream>

%<*symbol>
\begin{code}
data Symbol : Set where
  ■ : Symbol
  ◆ : Symbol
  ● : Symbol
\end{code}
%</symbol>

%<*s>
\begin{code}
s : ⟦ cStream ⟧ Symbol
s = tt , (λ _ → ◆)
\end{code}
%</s>

%<*l>
\begin{code}
l : ⟦ cList ⟧ Symbol
l = 3 , (λ  { zero                   → ■
            ; (suc zero)             → ●
            ; (suc (suc zero))       → ●
            ; (suc (suc (suc ()))) })
\end{code}
%</l>

%<*lprime>
\begin{code}
l' : ⟦ cList ⟧ Symbol
l' = cons ■ (cons ● (cons ● nil))
\end{code}
%</lprime>


%<*treeSh>
\begin{code}
data TreeSh : Set where
  leafSh : TreeSh
  nodeSh : TreeSh → TreeSh → TreeSh
\end{code}
%</treeSh>


%<*treePos>
\begin{code}
data TreePos : TreeSh → Set where
  leafPos : TreePos leafSh
  nodePosL : ∀{l r} → TreePos l → TreePos (nodeSh l r)  
  nodePosR : ∀{l r} → TreePos r → TreePos (nodeSh l r)  
\end{code}
%</treePos>


%<*ctree>
\begin{code}
cTree : Cont
cTree = TreeSh ◃ TreePos
\end{code}
%</ctree>

%<*tree>
\begin{code}
Tree : Set → Set
Tree = ⟦ cTree ⟧

leaf : ∀{X} → X →  ⟦ cTree ⟧ X
leaf x = leafSh , (λ { leafPos → x })

node : ∀{X} → ⟦ cTree ⟧ X → ⟦ cTree ⟧ X → ⟦ cTree ⟧ X
node (sl , pl) (sr , pr) = nodeSh sl sr , (λ  { (nodePosL pos) → pl pos
                                              ; (nodePosR pos) → pr pos })
\end{code}
%</tree>

%<*morph>
\begin{code}
record _⇒_ (C₁ C₂ : Cont) : Set where
  constructor _,_
  field
    mSh  : Sh C₁ → Sh C₂
    mPos : ∀{s : Sh C₁} → Pos C₂ (mSh s) → Pos C₁ s
\end{code}
%</morph>

\begin{code}
infixr 4 _⇒_
open _⇒_
\end{code}

%<*morphExt>
\begin{code}
⟦_⟧ₘ : ∀{C D} → (C ⇒ D) → ∀{X} → ⟦ C ⟧ X → ⟦ D ⟧ X
⟦ f ⟧ₘ ( c , fp ) = (mSh f c) , (fp ∘ mPos f {c})
\end{code}
%</morphExt>

%<*chead>
\begin{code}
chead : cList ⇒ cMaybe
chead =  (λ { zero → false  ; (suc _) → true }) ,
         (λ { {zero} ()     ; {suc _} _ → zero })
\end{code}
%</chead>


%<*head>
\begin{code}
head : ∀{X} → ⟦ cList ⟧ X → ⟦ cMaybe ⟧ X
head =  ⟦ chead ⟧ₘ
\end{code}
%</head>


%<*behead>
\begin{code}
behead : cList ⇒ cList
behead = (λ { zero → zero ; (suc x) → x }) , (λ { {zero} () ; {suc _} x → suc x })
\end{code}
%</behead>



%<*either>
\begin{code}
Either : Cont → Cont → Cont
Either C D = (Sh C ⊎ Sh D) ◃ [ Pos C , Pos D ]
\end{code}
%</either>

%<*inj1>
\begin{code}
ι₁ : ∀{C D} → C ⇒ Either C D
ι₁ = inj₁ , id
\end{code}
%</inj1>

\begin{code}
ι₂ : ∀{C D} → D ⇒ Either C D
ι₂ = inj₂ , id
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
