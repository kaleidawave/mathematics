import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Addition
import Mathematics.Structures.Numbers.Integer.Sign
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Ordering
import Mathematics.Structures.Numbers.Natural.Addition

open Natural in
def Integer.le (a b: Integer): Prop := Quotient.liftOn₂
  a b
  (fun (b, a) (d, c) => a + d <= c + b)
  (by
    intro (a, b) (c, d) (e, f) (g, h) h1 h2
    change b + e = f + a at h1
    change d + g = h + c at h2
    simp
    constructor
    {
      intro h3
      rw [
        add_left a,
        add_left d,
        Natural.add_commutative f,
        Natural.add_associative g,
        Natural.add_commutative,
        ←Natural.add_associative,
        ←h1,
        h2,
        Natural.add_associative,
        Natural.add_associative,
        Natural.add_associative,
        ←add_right,
        ←Natural.add_associative,
        Natural.add_commutative _ e,
        ←add_right,
        Natural.add_commutative c,
        Natural.add_commutative a,
      ]
      exact h3
    }
    {
      intro h3
      rw [
        add_left e,
        add_left h,
        Natural.add_commutative b,
        Natural.add_associative c,
        Natural.add_commutative c,
        Natural.add_associative,
        Natural.add_commutative c,
        h1,
        ←h2,
        Natural.add_commutative f,
        Natural.add_commutative d a,
        Natural.add_associative,
        Natural.add_associative,
        Natural.add_associative,
        ←add_right,
        ←Natural.add_associative,
        Natural.add_commutative f d,
        Natural.add_associative,
        ←add_right,
        Natural.add_commutative e,
      ]
      exact h3
    }
  )

instance : LE Integer := ⟨Integer.le⟩
instance : LT Integer := ⟨fun a b => a.successor <= b⟩

theorem lt_nat (a b: Integer): (a.successor <= b) = (a < b) := rfl

theorem le_nat (a b: Integer) (h1: a <= b): ∃c: Natural, a + c = b := by
  -- TODO is their a shorter way of doing this?
  cases a using Quotient.ind
  cases b using Quotient.ind
  rename_i x y
  let (b, a) := x
  let (d, c) := y

  obtain ⟨off, h1⟩ := h1
  exists off
  apply Quotient.sound
  change a + off + d = c + (b + 0)
  rw [Natural.add_zero]
  ac_nf at h1 |-

theorem le_nat2 (a b: Integer) (h1: ∃c: Natural, a + c = b): a <= b := by
  -- TODO is their a shorter way of doing this?
  cases a using Quotient.ind
  cases b using Quotient.ind
  rename_i x y
  let (b, a) := x
  let (d, c) := y

  obtain ⟨off, h1⟩ := h1
  change a + d <= c + b
  change Integer.add _ _ = _ at h1
  unfold Integer.add at h1
  replace h1 := Quotient.exact h1
  change _ = _ at h1
  exists off
  rw [Natural.add_zero] at h1
  simp at h1
  ac_nf at h1 |-

theorem if_eq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = a): c := by
  split at h2
  assumption
  exact h1 h2.symm |>.elim

theorem if_neq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = b): ¬c := by
  split at h2
  exact h1 h2 |>.elim
  assumption

theorem positive_greater_than (a: Integer): 0 <= a ↔ a.sign = Sign.positive := by
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold Integer.sign
  constructor
  {
    intro h1
    obtain ⟨c, h2⟩ := le_nat _ _ h1
    replace h2 := Quotient.exact h2
    apply if_pos
    change _ = _ at h2
    simp at h2
    rw [Natural.add_zero, Natural.zero_add, Natural.add_commutative, Natural.add_zero] at h2
    exists c
  }
  {
    intro h1
    replace h1: (if a ≤ b then Sign.positive else Sign.negative) = Sign.positive := h1
    change 0 + a <= b + 0
    rw [Natural.add_zero, Natural.zero_add]
    exact if_eq_reduction _ _ _ Sign.ne h1
  }

theorem negative_less_than (a: Integer): a < 0 ↔ a.sign = Sign.negative := by
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold Integer.sign
  constructor
  {
    intro h1
    obtain ⟨c, h2⟩ := le_nat _ _ h1
    replace h2 := Quotient.exact h2
    apply if_neg
    intro h3
    obtain ⟨c2, h3⟩ := h3
    change PairEq _ _ at h2
    unfold PairEq at h2
    simp at h2
    rw [Natural.add_zero, Natural.add_zero, Natural.add_zero, Natural.zero_add] at h2
    rw [←h2, Natural.add_associative, Natural.add_associative] at h3
    conv at h3 => rhs; rw [←Natural.add_zero b]
    rw [Natural.add_left_cancel, Natural.add_commutative, Natural.add_one] at h3
    contradiction
  }
  {
    intro h1
    have h2: (if a ≤ b then Sign.positive else Sign.negative) = Sign.negative := h1
    change Integer.le _ _
    unfold Integer.le Integer.successor
    rw [←Integer.one a]
    have h3 := if_neq_reduction _ _ _ Sign.ne h2
    change _ + _ <= _ + _
    simp
    rw [Natural.add_zero, Natural.zero_add]
    obtain ⟨c2, h3⟩ := Natural.less_than_not_greater_than.mpr h3
    rw [add.successor, ←successor.add]
    exists c2
    rw [Natural.add_associative, Natural.add_commutative a, ←Natural.add_associative, h3]
  }

instance (p q : Integer) : Decidable (p <= q) :=
  Quotient.recOnSubsingleton₂ p q (fun (b, a) (d, c) => inferInstanceAs (Decidable (a + d <= c + b)))
