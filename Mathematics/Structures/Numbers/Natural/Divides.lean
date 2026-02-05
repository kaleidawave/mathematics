import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Inequality

def divides (n: Natural) (result: Natural) : Prop := ∃m: Natural, m * n = result

-- infix:40 " ∣ " => divides

instance : Dvd Natural := ⟨divides⟩

theorem divides.def (a n: Natural) : a ∣ n ↔ ∃m: Natural, m * a = n := ⟨id, id⟩

example : (4: Natural) ∣ 8 := ⟨2, rfl⟩

theorem divides.zero (n: Natural) : n ∣ 0 := ⟨0, Natural.zero_multiply n⟩
theorem one.divides (n: Natural) : 1 ∣ n := ⟨n, Natural.multiply_one n⟩
theorem divides.self (n: Natural) : n ∣ n := ⟨1, Natural.one_multiply n⟩

theorem zero_div (n: Natural): (0 ∣ n) ↔ n = 0 := by
  constructor
  {
    intro ⟨a, h1⟩
    rw [Natural.multiply_zero] at h1
    exact h1.symm
  }
  {
    intro h1
    rw [h1]
    exact divides.zero 0
  }

theorem zero_div.false (n: Natural) (h1: n ≠ 0): ¬(0 ∣ n) := fun x => False.elim <| h1 <| (zero_div n).mp x

theorem divides.one (n: Natural) : n ∣ 1 ↔ n = 1 := by
  constructor
  {
    intro ⟨a, h1⟩
    exact (Natural.multiply_eq_one _ _ h1).right
  }
  intro h1; rw [h1]; exact one.divides 1

theorem divides.multiple (a b c d: Natural) (h1: a ∣ b) (h2: c ∣ d) : a * c ∣ b * d := by
  obtain ⟨e, h1⟩ := h1
  obtain ⟨g, h2⟩ := h2
  exists (e * g)
  rw [←h1, ←h2, Natural.multiply_associative];
  conv => rhs; rw [Natural.multiply_associative, ←Natural.multiply_associative a, Natural.multiply_commutative a, Natural.multiply_associative]
-- theorem divides.multiple₂ (n m: Natural) : n ∣ m * n := ⟨m, rfl⟩

theorem divides.transitivity (a b c: Natural) (h1: a ∣ b) (h2: b ∣ c) : a ∣ c := by
  let ⟨m, p⟩ := h1
  let ⟨n, q⟩ := h2
  rw [←q, ←p]
  exact ⟨
    m * n, by rw [←Natural.multiply_associative n m a, Natural.multiply_commutative n m]
  ⟩

theorem divides.swap (a b: Natural) : (a ∣ b) ∧ (b ∣ a) ↔ a = b := by
  constructor
  {
    intro ⟨⟨c, h1⟩, ⟨d, h2⟩⟩
    sorry -- interesting multiplication problem!!
    -- induction a with
    -- | zero => rw [Natural.multiply_zerod] at h1; exact h1
    -- | successor a ih => {
    --   -- rw [multiply.successor] at h1
    --   -- rw [←h1]
    -- }
  }
  {
    intro h1; rw [h1]; exact ⟨divides.self b, divides.self b⟩
  }

theorem divides.less_than (a b: Natural) (h1: a ∣ b) (h2: b ≠ 0): a <= b := by
  obtain ⟨c, h1⟩ := h1
  rw [←h1] at h2
  have ⟨c_neq, h3⟩ := (multiply.neq.zero _ _).mp h2
  rw [←h1]
  clear h1 h2 h3
  -- General result
  induction a with
  | zero => rw [Natural.multiply_zerod]; exact ⟨0, rfl⟩
  | successor a ih => {
    rw [multiply.successor]
    replace ih : a.successor ≤ (c * a).successor := Natural.less_than.equal.successor.l ih
    have c_gte_one : 1 <= c := Natural.less_than.equal.neq_one c c_neq
    have d := Natural.less_than.equal.add c_gte_one ih
    rw [Natural.add_one, successor.add] at d
    exact (Natural.less_than.equal.successor a.successor (c * a + c)).mpr d
  }

-- Is this something related to Bezout?
open Natural in
theorem divides.exists_integers (a b c: Natural) (h1: a ∣ b) (h2: a ∣ c) : ∀x y, a ∣ (b * x + c * y) := by
  obtain ⟨r, h1⟩ := h1
  obtain ⟨s, h2⟩ := h2
  intro x y
  exists (r * x + s * y)
  rw [
    multiply_distributive_right,
    ←multiply_associative,
    multiply_commutative a r,
    h1,
    ←multiply_associative,
    multiply_commutative a s,
    h2
  ]

theorem divides.not_eq_zero (n m: Natural) (h1: m ≠ 0) : n ∣ m → n ≠ 0 := by
  rintro ⟨d, h2⟩ h3
  rw [h3, Natural.multiply_zero] at h2
  exact h1 h2.symm
