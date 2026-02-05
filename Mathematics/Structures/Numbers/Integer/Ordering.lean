import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Sign
import Mathematics.Structures.Numbers.Integer.Inequality

theorem tricotomy (a: Integer): a < 0 ∨ a = 0 ∨ a > 0 := by
  cases h1: a.sign with
  | positive =>
    right;
    have d := positive_greater_than a |>.mpr h1
    obtain ⟨c, h2⟩ := le_nat 0 a d
    rw [Integer.add_commutative, Integer.add_zero] at h2
    cases a using Quotient.ind
    rename_i a
    let (b, a) := a
    induction c with
    | zero => rw [←h2]; left; rfl
    | successor c ih =>
      right
      change 0 < _
      rw [←lt_nat]
      apply le_nat2
      exists c
  | negative => {
    left;
    exact (negative_less_than a).mpr h1
  }
