open import Category
open import Category.Funtor
open import Extras

module Category.Representables {o a : Level}(𝓒 : Category {o} {a}) where

open import Category.Examples.Sets
open import Category.Product

open Category.Category
open Category.Product.HasProducts

Hom₁Prod : ∀{p : HasProducts 𝓒}{Y Z} → Functor (𝓒 ᴼᵖ) 𝑺𝒆𝒕
Hom₁Prod {p}{Y}{Z} = record
    { FObj =  λ X → Hom 𝓒 (Prod p X Y) Z
    ; FHom =  λ f h → comp 𝓒 h (pmap p f (iden 𝓒))
    ; idenPr = ext (λ a → trans (cong (comp 𝓒 a) (pmapIdId≅Id {𝓒 = 𝓒} {p})) (idr 𝓒 {f = a}))
    ; compPr = ext (λ a → trans (cong (comp 𝓒 a) (pmapComp≅compPmap {𝓒 = 𝓒} {p})) (ass 𝓒))
    }
    where open ≅-Reasoning
          pmapIdId≅Id : ∀  {𝓒 : Category} {p : HasProducts 𝓒}{Y X : Obj 𝓒}
                        →  pmap p (iden (𝓒 ᴼᵖ)) (iden 𝓒) ≅  iden 𝓒 {Prod p Y X}
          pmapIdId≅Id {𝓒 = 𝓒} {p} {X} {Y} = begin
                           idᴼᵖ ×̂ id    ≅⟨ cong₂ {a} {a} ⟨_,_⟩ (idl 𝓒) (idl 𝓒) ⟩
                           ⟨ π₁ , π₂ ⟩  ≅⟨ sym (pairUnique p (idr 𝓒) (idr 𝓒) ) ⟩
                           id
                           ∎
                           where _×̂_   = pmap p
                                 ⟨_,_⟩ = pair p
                                 π₁    = HasProducts.projl p
                                 π₂    = HasProducts.projr p
                                 id    = iden 𝓒
                                 idᴼᵖ  = iden (𝓒 ᴼᵖ)
          pmapComp≅compPmap : ∀ {𝓒 : Category}
                                {p : HasProducts 𝓒}
                                {X X' Y Z : Obj 𝓒}{f : Hom 𝓒 Y Z} {g : Hom 𝓒 X Y}
                              → pmap p (comp 𝓒 f g) (iden 𝓒) ≅ comp 𝓒 (pmap p {Y = X'} f (iden 𝓒)) (pmap p g (iden 𝓒))
          pmapComp≅compPmap {𝓒 = 𝓒} {p} {f = f} {g} = sym (pairUnique p
                               (begin
                                  π₁ ∘̂ ((f ×̂ id) ∘̂ (g ×̂ id))
                                ≅⟨ ass 𝓒 ⟩
                                  (π₁ ∘̂ (f ×̂ id)) ∘̂ (g ×̂ id) 
                                ≅⟨ cong (λ x → x ∘̂ (g ×̂ id)) (pairIdl p (f ∘̂ π₁) (id ∘̂ π₂))  ⟩
                                  (f ∘̂ π₁) ∘̂ (g ×̂ id)
                                ≅⟨ sym (ass 𝓒) ⟩
                                  f ∘̂ (π₁ ∘̂ (g ×̂ id))
                                ≅⟨ cong (λ x → f ∘̂ x ) (pairIdl p (g ∘̂ π₁) (id ∘̂ π₂))  ⟩
                                  f ∘̂ (g ∘̂ π₁)
                                ≅⟨ ass 𝓒 ⟩
                                  (f ∘̂ g) ∘̂ π₁
                                  ∎ )
                                (begin
                                  π₂ ∘̂ ((f ×̂ id) ∘̂ (g ×̂ id))
                                ≅⟨ ass 𝓒 ⟩
                                  (π₂ ∘̂ (f ×̂ id)) ∘̂ (g ×̂ id) 
                                ≅⟨ cong (λ x → x ∘̂ (g ×̂ id)) (pairIdr p (f ∘̂ π₁) (id ∘̂ π₂))  ⟩
                                  (id ∘̂ π₂) ∘̂ (g ×̂ id)
                                ≅⟨ cong (λ x → x ∘̂ (g ×̂ id)) (idl 𝓒) ⟩
                                  π₂ ∘̂ (g ×̂ id)
                                ≅⟨ pairIdr p (g ∘̂ π₁) (id ∘̂ π₂) ⟩
                                  id ∘̂ π₂
                                  ∎) )
                                  where π₁    = HasProducts.projl p
                                        π₂    = HasProducts.projr p
                                        _∘̂_   = comp 𝓒
                                        _×̂_   = pmap p
                                        id    = iden 𝓒
