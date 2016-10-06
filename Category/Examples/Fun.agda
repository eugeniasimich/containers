module Category.Examples.Fun where

open import Category as C
open import Category.Funtor
open import Category.Natural
open import Extras

open Category.Funtor.Functor
open Category.Natural.NaturalTransformation
      

natIden : ∀{o a}{𝓒 𝓓 : Category {o} {a}}{F : Functor 𝓒 𝓓} → NaturalTransformation {𝓒 = 𝓒} {𝓓} F F
natIden {𝓒 = 𝓒} {𝓓} {F} = let open C.Category 𝓓 in record
    { η    = iden
    ; nat  = trans idr (sym $ idl)}

natCompose : ∀{o a}{𝓒 𝓓 : Category {o} {a}}
           →  {F G H : Functor 𝓒 𝓓}
           →  (α : NaturalTransformation G H) → (β : NaturalTransformation F G)
           →  NaturalTransformation F H
natCompose {𝓓 = 𝓓} {F} {G} {H} α β = let open C.Category 𝓓  in record
    { η    =  comp (η α) (η β)
    ; nat  = λ  {A B f} → begin 
                     comp (FHom H f) (comp (η α) (η β))
                  ≅⟨ ass ⟩
                     comp (comp (FHom H f) (η α)) (η β)
                  ≅⟨ cong (λ x → comp x (η β)) (nat α) ⟩
                     comp (comp (η α) (FHom G f)) (η β)
                  ≅⟨ sym ass  ⟩
                     comp (η α) (comp (FHom G f) (η β))
                  ≅⟨ cong (comp (η α)) (nat β) ⟩
                     comp (η α) (comp (η β) (FHom F f))
                  ≅⟨ ass ⟩
                     comp (comp (η α) (η β)) (FHom F f)
                  ∎ }
    where open ≅-Reasoning
         

NatT≅ : ∀{o a o' a'}{C : Category {o}{a}}{D : Category {o'}{a'}}{F G : Functor C D}
         {α β : NaturalTransformation F G} → 
         (λ {X} → η α {X}) ≅ (λ{X} → η β {X}) → 
         α ≅ β
NatT≅ {C = 𝓒}{D = 𝓓}{F}{G}{α = η , nat} {.η , nat₁} refl = cong {A =  ∀{A B}{f : Hom 𝓒 A B} →  comp 𝓓 (FHom G f) η ≅ comp 𝓓 η (FHom F f)}
                                                                 {λ x → NaturalTransformation F G}
                                                                 (λ x → (η , x)) (iext (iext (iext ir)))
      where open C.Category
      
𝑭𝒖𝒏 : ∀{o a} → Category {o} {a} → Category → Category
𝑭𝒖𝒏 𝓒 𝓓 = let open C.Category 𝓓 in record
    { Obj   = Functor 𝓒 𝓓
    ; Hom   = NaturalTransformation
    ; iden  = natIden 
    ; comp  = natCompose
    ; idl   = NatT≅ (iext idl)
    ; idr   = NatT≅ (iext idr)
    ; ass   = NatT≅ (iext ass) }

