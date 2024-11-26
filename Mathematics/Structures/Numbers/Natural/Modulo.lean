import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication

def Natural.modulo_congruence (a b m : Natural) : Prop := ∃n: Natural, b = m * n + a

-- TODO fix precedence
notation a " ≡ " b " mod " m  => Natural.modulo_congruence a b m

example : 5 ≡ 7 mod 2 := ⟨1, rfl⟩

theorem add (a b m : Natural) : (a ≡ b mod m) → (a ≡ (b + m) mod m) := by
  intro h1
  let ⟨n, h2⟩ := h1
  apply Exists.intro (n + 1)
  rw [
    h2,
    multiply.add,
    multiply.one,
    ←Natural.add.associative,
    ←Natural.add.commutative m,
    ←Natural.add.associative
  ]

theorem multiply (a b m n: Natural) : (a ≡ b mod m) → ((n * a) ≡ n * b mod m) := by
  intro h1
  let ⟨n2, h2⟩ := h1
  apply Exists.intro (n2 * n)
  rw [
    h2,
    multiply.distributive,
    multiply.commutative,
    multiply.associative
  ]
