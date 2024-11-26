import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Divides
import Mathematics.Structures.Numbers.Natural.Inequality

def Natural.is_prime (p: Natural) := p != 1 ∧ ∀a: Natural, a ∣ p → a = 1 ∨ a = p

/- Weak left cancelation -/
theorem mul_must_be_one (a b: Natural) (h1: a ≠ 0) : a = a * b → b = 1 := by
  cases b with
  | zero => rw [Natural.zero_def, multiply.zero]; intro h1; contradiction
  | successor b => {
    intro h2
    conv at h2 => rw [multiply.successor]; lhs; rw [←Natural.zero.add a];
    rw [add.left_cancel] at h2
    have d := multiply.eq.zero _ _ h2.symm
    cases d with
    | inl h => contradiction
    | inr h => rw [h]; rfl
  }

theorem even_not_prime (n: Natural) (h1: n ≠ 1) : ¬(Natural.is_prime (2 * n)) := by
  rintro ⟨_, h2⟩
  have h3 : 2 ∣ 2 * n := ⟨n, by rw [multiply.commutative]⟩
  have h4 := (h2 2) h3
  cases h4 with
  | inl h => contradiction
  | inr h => {
    have d := (mul_must_be_one 2 n) (by exact Ne.symm (ne_of_beq_false rfl)) h
    exact h1 d
  }

theorem greater_than_two (n: Natural) : 2 <= n → n ≠ 0 ∧ n ≠ 1 := by
  rintro ⟨w, h1⟩
  exact ⟨
    by
      intro h2;
      rw [h2] at h1;
      contradiction,
    by
      intro h2;
      have b: (2: Natural) = 1 + 1 := rfl
      rw [h2, ←Natural.add.zero 1, b, ←Natural.add.associative, add.right_cancel _ 1 _, Natural.add.commutative, add.one] at h1;
      exact successor.neq.zero w h1
  ⟩

theorem multiple_not_prime (m n: Natural) (h1: n ≠ 1) (h2: 2 <= m) : ¬(Natural.is_prime (m * n)) := by
  rintro ⟨_, h3⟩
  have ⟨lhs, rhs⟩ := greater_than_two m h2
  have h4 : m ∣ m * n := ⟨n, by rw [multiply.commutative]⟩
  have h5 := (h3 m) h4
  cases h5 with
  | inl h => exact rhs h
  | inr h => {
    have d := (mul_must_be_one m n) lhs h
    exact h1 d
  }
