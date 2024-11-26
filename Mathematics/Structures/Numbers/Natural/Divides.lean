import Mathematics.Structures.Numbers.Natural.Multiplication

def divides (n: Natural) (result: Natural) : Prop := ∃m: Natural, m * n = result

-- infix:40 " ∣ " => divides

instance : Dvd Natural := ⟨divides⟩

example : (4: Natural) ∣ 8 := ⟨2, rfl⟩

theorem divides.self (n: Natural) : n ∣ n := ⟨1, one.multiply n⟩
theorem divides.multiple (n m: Natural) : n ∣ m * n := ⟨m, rfl⟩

theorem one.divides (n: Natural) : 1 ∣ n := ⟨n, multiply.one n⟩

theorem divides.transitivity (a b c: Natural) (h1: a ∣ b) (h2: b ∣ c) : a ∣ c := by
  let ⟨m, p⟩ := h1
  let ⟨n, q⟩ := h2
  rw [←q, ←p]
  exact ⟨
    m * n, by rw [←multiply.associative n m a, multiply.commutative n m]
  ⟩

theorem divides.not_eq_zero (n m: Natural) (h1: m ≠ 0) : n ∣ m → n ≠ 0 := by
  rintro ⟨d, h2⟩ h3
  rw [h3, multiply.zero] at h2
  exact h1 h2.symm
