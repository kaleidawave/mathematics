import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Subtraction
import Mathematics.Structures.Numbers.Natural.Multiplication
-- import Mathematics.Structures.Numbers.Natural.Power
-- import Mathematics.Structures.Numbers.Natural.Prime
import Mathematics.Structures.Numbers.Natural.Divides
-- import Mathematics.Structures.Numbers.Natural.Inequality

-- This is only naturals

def Natural.modulo_congruence (a b m : Natural) : Prop := m ∣ (Natural.difference a b)

-- TODO fix precedence
notation a:10 " ≡ " b:20 " mod " m:10  => Natural.modulo_congruence a b m

example : 5 ≡ 7 mod 2 := ⟨1, rfl⟩
example : 7 ≡ 5 mod 2 := ⟨1, rfl⟩

theorem mc.refl (a m: Natural) : a ≡ a mod m := by
  unfold Natural.modulo_congruence
  rw [Difference.self a]
  exact divides.zero m

theorem mc.symmetric (a b m: Natural) (h1: a ≡ b mod m): b ≡ a mod m := by
  unfold Natural.modulo_congruence
  rw [Difference.symmetric]
  exact h1

#eval (fun a b c => (Natural.difference a b, Natural.difference b c, Natural.difference a c)) 3 1 3

theorem mc.transitive (a b c m: Natural) (h1: a ≡ b mod m) (h2: b ≡ c mod m): a ≡ c mod m := by
  obtain ⟨k1, h1⟩ := h1
  obtain ⟨k2, h2⟩ := h2
  unfold Natural.modulo_congruence
  exists (Natural.difference k1 k2)
  sorry
  /-
  induction m with
  | zero => {
    rw [multiply.zerod] at |- h1 h2
    have h3: a = b :=  Difference.self_iff a b (id (Eq.symm h1))
    have h4: b = c :=  Difference.self_iff b c (id (Eq.symm h2))
    have h5: a = c := Eq.trans h3 h4
    rw [h5]
    exact Eq.symm (Difference.self c)
  }
  | successor m ih => {
    rw [multiply.successor]
    sorry
  }
  -/

theorem mc.zero (a b: Natural) (h1: a ≡ b mod 0): a = b := by
  have h2 := (zero_div _).mp h1
  exact Difference.self_iff a b h2

theorem mc.add.left (a b c m : Natural) (h1: a ≡ b mod m): (a + c) ≡ (b + c) mod m := by
  obtain ⟨n, h2⟩ := h1
  exists n
  sorry
  -- rw [←add.associative, h2]

/-


theorem mc.add.multiple (a b m : Natural) (h1: a ≡ b mod m): (a ≡ (b + m) mod m) := by
  obtain ⟨n, h1⟩ := h1
  exists (n + 1)
  rw [
    h1,
    multiply.add,
    multiply.one,
    add.associative,
    ←add.commutative m,
    add.associative
  ]

theorem mc.add.multiple_m (a b c m : Natural) (h1: a ≡ b mod m): (a ≡ (b + c * m) mod m) := by
  obtain ⟨n, h1⟩ := h1
  exists (n + c)
  rw [
    multiply.add,
    add.associative,
    add.commutative _ a,
    ←add.associative,
    h1,
    multiply.commutative c
  ]

theorem mc.sub.left (a b c m : Natural) (h1: a ≡ b mod m): (a -ₛ c) ≡ (b -ₛ c) mod m := by
  obtain ⟨n, h2⟩ := h1
  exists n

  -- rw [←add.associative, h2]

theorem mc.add.right (a b c m : Natural) (h1: (a + c) ≡ (b + c) mod m): a ≡ b mod m := by
  obtain ⟨n, h2⟩ := h1
  exists n
  rw [←add.associative] at h2
  exact (add.right_cancel b c (m * n + a)).mp h2

theorem mc.add (a b c m : Natural): (a ≡ b mod m) ↔ (a + c) ≡ (b + c) mod m := ⟨
  mc.add.left a b c m,
  mc.add.right a b c m
⟩

theorem mc.multiply (a b m n: Natural) : (a ≡ b mod m) → ((n * a) ≡ n * b mod m) := by
  intro h1
  obtain ⟨n2, h2⟩ := h1
  exists (n2 * n)
  rw [
    h2,
    multiply.distributive,
    multiply.commutative,
    multiply.associative
  ]

theorem mc.multiply₂ (a b m n: Natural) : (a ≡ b mod m) ↔ (a ≡ b + (n * m) mod m) := by
  constructor
  {
    intro ⟨n2, h1⟩
    rw [h1, multiply.commutative, add.commutative _ a, add.associative]
    rw [multiply.commutative, multiply.commutative _ m,  ←multiply.add]
    exists (n2 + n)
    rw [add.commutative]
  }
  {
    intro ⟨n2, h1⟩
    unfold Natural.modulo_congruence
    exists (n2 -ₛ n)
    sorry
    -- rw [n]
  }

  -- let ⟨n2, h2⟩ := h1
  -- exists (n2 * n)
  -- rw [
  --   h2,
  --   multiply.distributive,
  --   multiply.commutative,
  --   multiply.associative
  -- ]

-- theorem sub (a b m n: Natural) : (a ≡ b mod m) → ((n * a) ≡ n * b mod m) := todo
-- theorem pow (a b m n: Natural) : (a ≡ b mod m) → ((n * a) ≡ n * b mod m) := todo

-- TODO quotient on Natural.modulo_congruence
-- TODO equiv to (a % m = b % m)

-- Can only prove this direction for naturals
theorem modulo.divides (n m: Natural) (h1: m ∣ n) : 0 ≡ n mod m := by
  obtain ⟨d, h1⟩ := h1
  exists d
  rw [multiply.commutative] at h1
  rw [h1, Natural.add.zero]

theorem TwoModulo (n: Natural) : (0 ≡ n mod 2) ∨ 1 ≡ n mod 2 := by
  cases EitherEven n with
  | inl h1 => {
    obtain ⟨a, h1⟩ := h1
    left
    rw [←h1]
    exact ⟨a, by rw [Natural.add.zero, multiply.commutative]⟩
  }
  | inr h1 => {
    right
    replace := modulo.divides _ _ h1
    obtain ⟨a, h1⟩ := h1
    have d := mc.add.right 1 n 2 2
    -- apply d
    -- exists a
    -- rw [multiply.commutative]
    -- rw [h1]

    -- rw [add.successor]

    -- induction a with
    -- | zero =>
    --   exists 0
    --   have d := Natural.zero_def ▸ zero.multiply
    --   rw [d, add.one] at h1
    --   contradiction
    -- | successor a ih => {
    --   -- exists a
    --   sorry
    --   -- rw [successor.multiply, multiply.two] at h1
    --   -- induction n with
    --   -- | zero => have d := Natural.zero_def ▸ zero.add; rw [d] at h1; contradiction
    --   -- | successor n ih => {
    --   --   sorry
    --   -- }
    -- }
    -- exists a
    -- sorry
    -- exact ⟨a, by rw [Natural.add.zero, multiply.commutative]⟩
    -- rw [←h1]
  }

theorem FermatsLittleTheorem (p: Prime) (a: Natural) : (a ^ p.val) ≡ a mod p.val := by sorry
-/
