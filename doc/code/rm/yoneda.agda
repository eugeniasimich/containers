


⟦ reader a ⇒ F ⟧ ≅ ⟦ F ⟧ a

∀x → ⟦ reader a ⟧ x → ⟦ F ⟧ x ≅ ⟦ F ⟧ a

id a = (a → x) → id x

list a = (a → x) → list x


f : (a → x) → F x
f id : F a

h : a → x
f h = map h (f id)


cont r a = ((a -> r) -> r) 
