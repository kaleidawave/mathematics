import Mathematics.Structures.Function

structure Bijection (T U: Type) where
f: T → U
f_invs: U → T
composition: f ∘ f_invs = id ∧ f_invs ∘ f = id

def identity (T: Type): Bijection T T := ⟨id, id, by constructor <;> rfl⟩

theorem bijection.injective {T U: Type} (b: Bijection T U): ∀x y: T, b.f x = b.f y → x = y := by
  intro x1 x2 h2
  rw [←identity_definition x1, ←identity_definition x2, ←b.composition.right, composition_definition, h2]
  rfl

theorem bijection.surjective {T U: Type} (b: Bijection T U): ∀y: U, ∃x: T, b.f x = y := by
  intro y
  exists b.f_invs y
  rw [←composition_definition b.f b.f_invs y, b.composition.left]
  exact identity_definition y

-- TODO non computable? above as classes?
