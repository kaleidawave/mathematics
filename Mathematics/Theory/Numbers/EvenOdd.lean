import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Divides

def IsEven (n: Natural): Prop := 2 ∣ n
def IsOdd (n: Natural): Prop := 2 ∣ n.successor

theorem NotEven (n: Natural) (h1: ¬IsEven n): IsOdd n := by
  unfold IsEven at h1
  unfold IsOdd
  induction n with
  | zero =>
    exact False.elim <| h1 <| divides.zero 2
  | successor n ih =>
    by_cases h2: 2 ∣ n
    {
      obtain ⟨m, h2⟩ := h2
      exists m.successor
      rw [successor.multiply, h2]
      have : 2 = (Natural.zero.successor.successor) := rfl
      rw [this, add.successor, add.successor, Natural.add_zerod]
    }
    exact False.elim <| h1 <| Natural.add_one n ▸ ih h2

theorem two_def : 2 = (Natural.zero.successor.successor) := rfl

-- TODO can we reuse the previous
theorem NotOdd (n: Natural) (h1: ¬IsOdd n): IsEven n := by
  unfold IsOdd at h1
  unfold IsEven
  induction n with
  | zero =>
    exact divides.zero 2
  | successor n ih =>
    by_cases h2: 2 ∣ n
    {
      rw [←add.two] at h1
      obtain ⟨d, h2⟩ := h2
      have : 2 ∣ n + 2 := by
        exists d.successor
        rw [successor.multiply, ←h2]
      contradiction
    }
    exact NotEven n h2

theorem NotEvenAndOdd (n: Natural): ¬(IsEven n ∧ IsOdd n) := by
  intro ⟨h1, h2⟩
  obtain ⟨a, h1⟩ := h1
  obtain ⟨b, h2⟩ := h2
  rw [←h1] at h2
  induction b with
  | zero => {
    contradiction
  }
  | successor b ih => {
    rw [successor.multiply] at h2
    induction a generalizing b
    sorry
    sorry
  }

-- TODO mutually exclusive
theorem Parity (n: Natural): IsEven n ∨ IsOdd n := by
  by_cases h: 2 ∣ n
  exact Or.inl h
  exact Or.inr (NotEven n h)

theorem EvenMul (a b: Natural) (h1: IsEven a): IsEven (a * b) := by
  obtain ⟨c, h1⟩ := h1
  exists (b * c)
  rw [Natural.multiply_associative, h1, Natural.multiply_commutative]

theorem OddMul (a b: Natural) (h1: IsOdd a) (h2: IsOdd b): IsOdd (a * b) := by
  obtain ⟨c, h1⟩ := h1
  obtain ⟨d, h2⟩ := h2
  exists (b * c + a * d)
  -- rw [
  --   multiply.distributive.right,
  --   multiply.commutative b,
  --   multiply.commutative c,
  --   ←multiply.associative,
  --   ←multiply.associative,

  --   -- h1,
  --   -- h2,
  -- ]
  sorry

theorem IsOddTwo (n: Natural): (IsOdd n) ↔ ∃c: Natural, (c + c).successor = n := by
  constructor
  {
    intro ⟨c, h1⟩
    cases n with
    | zero =>
      have d: False := by
        induction c with
        | zero => rw [zerod.multiply] at h1; contradiction
        | successor c ih => {
          rw [successor.multiply] at h1
          sorry
        }
      exact False.elim d
    | successor n => {
      rw [multiply.two] at h1
      cases c with
      | zero => sorry --contradiction
      | successor c => {
        rw [successor.add, add.successor] at h1
        exact ⟨c, successor.inj h1⟩
      }
    }
  }
  {
    intro ⟨c, h1⟩
    exists c.successor
    rw [←h1, successor.multiply]
    sorry -- trivial
  }

  -- rw [multiply.associative, h1, multiply.commutative]

inductive Even : Natural → Prop where
  | /-- 0 is considered even here -/
  zero : Even 0
  | /-- If `n` is even, then so is `n + 2`. -/
  plusTwo : Even n → Even (n + 2)

inductive Odd: Natural → Prop where
  | /-- 1 is considered odd here -/
  zero : Odd 1
  | /-- If `n` is even, then so is `n + 2`. -/
  plusTwo : Odd n → Odd (n + 2)
