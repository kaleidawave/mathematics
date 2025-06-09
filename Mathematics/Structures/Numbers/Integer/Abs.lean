import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Integer.Negation

def Integer.abs (Integer: Integer): Natural := Quotient.liftOn
  Integer
  (fun (a, b) => if a <= b then b -ₛ a else a -ₛ b)
  (by
    intro (a, b) (c, d) pair_eq
    change PairEq (a, b) (c, d) at pair_eq
    unfold PairEq at pair_eq
    simp at pair_eq |-
    cases Natural.lt_trichotomy a b with
    | inl h1 => {
      replace h1 : a <= b := Natural.less_than_implies_less_than_equal h1
      have h2: c <= d := by
        have ⟨n, h1n⟩ := h1
        rw [←h1n, Natural.add_commutative d, Natural.add_associative, Natural.add_left_cancel, Natural.add_commutative] at pair_eq
        exists n
      rw [
        if_pos h1,
        if_pos h2,
        subtraction_eq_iff_eq_add h1,
        Natural.add_commutative,
        Natural.subtraction.add3 b d c a h2,
        Natural.add_commutative a,
      ]
      exact pair_eq
    }
    | inr h1 => cases h1 with
    | inl h1 => {
      rw [h1] at |- pair_eq
      rw [Natural.add_commutative d, Natural.add_left_cancel] at pair_eq
      have b_lt: b <= b := Natural.less_than.equal.self b
      have c_lt: c <= d := pair_eq ▸ (Natural.less_than.equal.self _)
      rw [if_pos b_lt, if_pos c_lt, pair_eq, subtraction.self, subtraction.self]
    }
    | inr h1 => {
      have ⟨l, bd⟩ := h1
      rw [
        ←bd,
        successor.add, ←add.successor, ←Natural.add_associative, Natural.add_commutative _ b, Natural.add_associative,
        Natural.add_left_cancel, add.successor, ←successor.add
      ] at pair_eq
      have h2: c > d := ⟨l, pair_eq.symm⟩
      have h1: ¬(a <= b) := Natural.less_than_not_greater_than.mp h1
      have h2: ¬(c <= d) := Natural.less_than_not_greater_than.mp h2
      rw [if_neg h1, if_neg h2]
      rw [pair_eq, ←bd, Natural.add_commutative, Natural.add_commutative _ l]
      rw [add.successor, ←successor.add, subtraction_lhs_addition]
      rw [add.successor, ←successor.add, subtraction_lhs_addition]
    }
  )

theorem Integer.abs_zero: (0: Integer).abs = 0 := rfl
theorem Integer.abs_one: (1: Integer).abs = 1 := rfl
theorem Integer.abs_minus_one: (-1: Integer).abs = 1 := rfl

theorem Integer.abs_eq_zero (a: Integer): a.abs = 0 ↔ a = 0 := by
  constructor
  . intro h1;
    cases a using Quot.ind with
    | mk a =>
      let (a, b) := a;
      have h2: (if a <= b then b -ₛ a else a -ₛ b) = 0 := h1
      apply Quotient.sound
      split at h2
      case isTrue h1 =>
        change PairEq _ _
        unfold PairEq
        simp
        obtain ⟨c, ht⟩ := h1
        rw [←ht, Natural.add_commutative, subtraction_lhs_addition] at h2
        rw [h2, Natural.add_zero] at ht
        rw [←ht, Natural.add_commutative]
      case isFalse h1t =>
        have h1: a > b := by exact Natural.less_than_not_greater_than.mpr h1t
        obtain ⟨c, ht⟩ := h1
        rw [←ht, successor.add, ←add.successor, Natural.add_commutative, subtraction_lhs_addition] at h2
        contradiction
  . intro h1; rw [h1]; rfl

theorem if_map {T U: Type} (f: T → U): ∀(c: Bool) (a b: T), (f (if c then a else b)) = if c then f a else f b := fun c a b => apply_ite f (c = true) a b

theorem if_eq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = a): c := by
  split at h2
  assumption
  exact h1 h2.symm |>.elim

theorem if_neq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = b): ¬c := by
  split at h2
  exact h1 h2 |>.elim
  assumption

theorem Integer.abs_right (a: Natural): (Integer.mk (0, a) |>.abs) = a := by
  unfold abs
  suffices (if (0 <= a) then (a -ₛ 0) else (0 -ₛ a)) = a by assumption
  rw [if_pos (Natural.greater_than.equal.zero a), subtraction.rhs.zero]

theorem Integer.abs_left (a: Natural): (Integer.mk (a, 0) |>.abs) = a := by
  unfold abs
  suffices (if (a <= 0) then (0 -ₛ a) else (a -ₛ 0)) = a by assumption
  -- TODO
  by_cases h1: a <= 0;
  {
    rw [if_pos h1];
    have h2 : a = 0 := by exact Natural.less_than.equal.zero a h1
    rw [h2];
    exact subtraction.rhs.zero _
  }
  rw [if_neg h1]; rw [subtraction.rhs.zero]
