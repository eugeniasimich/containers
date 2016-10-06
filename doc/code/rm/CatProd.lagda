\begin{code}

module CatProd where

open import Cat
open import Level
open import Extras
open import Data.Product
open import Relation.Binary.HeterogeneousEquality

open Category
\end{code}


%<*prod>
\begin{code}
CatProd :  Category  → Category → Category
CatProd 𝓒 𝓓 = record
                { Obj = Obj 𝓒 × Obj 𝓓
                ; Hom = λ { (C , D) (C' , D') → Hom 𝓒 C C' × Hom 𝓓 D D' }
                ; iden = (iden 𝓒) , (iden 𝓓)
                ; comp = λ { (f₁ , f₂) (g₁ , g₂) → (comp 𝓒 f₁ g₁) , ((comp 𝓓 f₂ g₂))}
                ; idl = cong₂ _,_ (idl 𝓒) (idl 𝓓)
                ; idr = cong₂ _,_ (idr 𝓒) (idr 𝓓)
                ; ass = cong₂ _,_ (ass 𝓒) (ass 𝓓)
                }
\end{code}
%</prod>
