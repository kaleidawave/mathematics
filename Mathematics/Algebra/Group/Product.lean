import Mathematics.Algebra.Group

def Group.Product (A B: Type) [Group A] [Group B] : Type := A × B

instance (A B: Type) [Group A] [Group B] : Mul (Group.Product A B) := ⟨fun (g1, g2) (h1, h2) => (g1 * h1, g2 * h2)⟩
instance (A B: Type) [Group A] [Group B] : Inverse (Group.Product A B) := ⟨fun (g1, g2) => (g1⁻¹, g2⁻¹)⟩
instance (A B: Type) [Group A] [Group B] : OfNat (Group.Product A B) 1 := ⟨(1, 1)⟩

theorem mul_eq (A B: Type) [Group A] [Group B] (a b: Group.Product A B) : a * b = (a.1 * b.1, a.2 * b.2) := rfl
theorem mul_inv (A B: Type) [Group A] [Group B] (a: Group.Product A B) : a⁻¹ = (a.1⁻¹, a.2⁻¹) := rfl
theorem one_left (A B: Type) [Group A] [Group B] : (1: Group.Product A B) = (1, 1) := rfl

instance (A B: Type) {ga: Group A} {gb: Group B} : Group (Group.Product A B) := {
  associativity := by
    intro a b c
    rw [mul_eq, mul_eq, ga.associativity, gb.associativity]
    rfl
  inverse := by
    intro a
    rw [mul_inv, mul_eq, (ga.inverse _).1, (gb.inverse _).1, mul_eq, (ga.inverse _).2, (gb.inverse _).2]
    exact ⟨one_left _ _, one_left _ _⟩
  identity := by
    intro a
    rw [mul_eq, one_left, (ga.identity _).1, (gb.identity _).1, mul_eq, (ga.identity _).2, (gb.identity _).2]
    exact ⟨rfl, rfl⟩
}
