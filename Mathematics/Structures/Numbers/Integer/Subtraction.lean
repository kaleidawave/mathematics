import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Addition
import Mathematics.Structures.Numbers.Integer.Negation

def Integer.sub (a b: Integer): Integer := a + -b

instance : Sub Integer := ⟨Integer.sub⟩

theorem Integer.sub.self (a: Integer) : a - a = 0 := by
  cases a using Quotient.ind
  apply Quotient.sound
  change PairEq _ _
  rename_i a
  let (a, b) := a
  simp
  rw [Natural.add_zero, Natural.zero_add]
  ac_nf

theorem Integer.sub.zero (a: Integer) : a - 0 = a := by
  cases a using Quotient.ind
  apply Quotient.sound
  change PairEq _ _
  rename_i a
  let (a, b) := a
  unfold PairEq
  simp
  rw [Natural.add_zero, Natural.add_zero]

theorem Integer.add_sub.associative (a b c: Integer) : a + (b - c) = (a + b) - c := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  cases c using Quotient.ind
  apply Quotient.sound
  simp
  ac_rfl

theorem Integer.neg_add (a b: Integer) : -(a + b) = -a + -b := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound
  rfl

theorem add_cancel (a b c: Integer) (h1: a = b + c): a - c = b := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  cases c using Quotient.ind
  -- rename_i a b c
  -- let (a1, a2) := a
  -- let (b1, b2) := b
  -- let (c1, c2) := c

  replace h1 := Quotient.exact h1
  apply Quotient.sound
  change _ = _ at h1 |-
  simp
  ac_nf at h1 |-
