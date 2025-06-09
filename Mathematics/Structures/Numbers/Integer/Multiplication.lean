import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Abs
import Mathematics.Structures.Numbers.Integer.Sign
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Integer.Negation
import Mathematics.Structures.Numbers.Integer.Addition

def Integer.mul (a b: Integer): Integer := match a.sign, b.sign with
| Sign.positive, Sign.positive => Integer.mk (0, a.abs * b.abs)
| Sign.negative, Sign.negative => Integer.mk (0, a.abs * b.abs)
| Sign.positive, Sign.negative => Integer.mk (a.abs * b.abs, 0)
| Sign.negative, Sign.positive => Integer.mk (a.abs * b.abs, 0)

def Integer.mul2 (a b: Integer): Integer := if
  a.sign == b.sign
  then Integer.mk (0, a.abs * b.abs)
  else Integer.mk (a.abs * b.abs, 0)

theorem MulEqDev (a b: Integer): Integer.mul a b = Integer.mul2 a b := by
  unfold Integer.mul Integer.mul2
  match a.sign, b.sign with
  | Sign.positive, Sign.positive => rw [if_pos]; rfl
  | Sign.negative, Sign.negative => rw [if_pos]; rfl
  | Sign.positive, Sign.negative => rw [if_neg]; exact Sign.neq rfl
  | Sign.negative, Sign.positive => rw [if_neg]; exact Sign.neq rfl

instance : Mul Integer := ⟨Integer.mul⟩

theorem Integer.mul_comm (a b: Integer): a * b = b * a := by
  change Integer.mul _ _ = Integer.mul _ _
  rw [MulEqDev, MulEqDev]
  unfold mul2
  have d : ∀p1 p2: Sign, p1 = p2 ∨ p1 ≠ p2 := by
    intro p1 p2
    match p1, p2 with
    | Sign.positive, Sign.positive => left; rfl
    | Sign.negative, Sign.negative => left; rfl
    | Sign.positive, Sign.negative => right; exact Sign.noConfusion
    | Sign.negative, Sign.positive => right; exact Sign.noConfusion

  cases Sign.binary_relation a.sign b.sign with
  | inl h1 => rw [if_pos h1, if_pos <| Sign.comm ▸ h1]; rw [Natural.multiply_commutative];
  | inr h1 => {
    have n1 := Sign.neq h1
    have n2 := Sign.neq <| Sign.neq_comm ▸ h1
    rw [if_neg n1, if_neg n2, Natural.multiply_commutative];
  }

#print axioms Integer.mul_comm

theorem Integer.mul_pos (a b: Integer) (h1: a.sign = Sign.positive) (h2: b.sign = Sign.positive):
  (a * b).sign = Sign.positive
:= by
  change (mul _ _).sign = Sign.positive
  unfold mul
  rw [h1, h2]
  suffices (if 0 <= a.abs * b.abs then Sign.positive else Sign.negative) = Sign.positive by assumption
  rw [if_pos (Natural.greater_than.equal.zero _)]

theorem Integer.abs_mul (a b: Integer): (a * b).abs = a.abs * b.abs := by
  conv in (_ * _) => change Integer.mul _ _; unfold mul
  match a.sign, b.sign with
  | Sign.positive, Sign.positive => rw [Integer.abs_right];
  | Sign.negative, Sign.negative => rw [Integer.abs_right];
  | Sign.negative, Sign.positive => rw [Integer.abs_left];
  | Sign.positive, Sign.negative => rw [Integer.abs_left];

theorem Integer.mul_zero (a: Integer): a * 0 = 0 := by
  change Integer.mul a 0 = _
  unfold mul
  rw [Integer.abs_zero, Natural.multiply_zero, Integer.mk_zero]
  split <;> rfl

theorem Integer.mul_minus_one (a: Integer): a * -1 = -a := by
  change Integer.mul a _ = Integer.negate _
  unfold mul
  have h1 : (-1: Integer).sign = Sign.negative := rfl
  rw [Integer.abs_minus_one, Natural.multiply_one, h1]
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold negate
  split
  contradiction
  -- change _ = (Integer.mk (b, a))
  sorry
  sorry
  sorry

theorem Integer.mul_add (a b c: Integer): a * (b + c) = a * b + a * c := by
  change Integer.mul _ (Integer.add b c) = _
  sorry
  -- unfold mul add

  -- match b.sign, c.sign with
  -- | Sign.positive, Sign.positive => sorry
  -- | Sign.negative, Sign.positive => sorry
  -- | Sign.negative, Sign.negative => sorry
  -- | Sign.positive, Sign.negative => sorry

theorem Integer.mul_assoc (a b c: Integer): a * (b * c) = (a * b) * c := by
  change Integer.mul _ _ = Integer.mul _ _
  unfold mul
  rw [abs_mul, abs_mul, ←Natural.multiply_associative]
  match a.sign, c.sign with
  | Sign.positive, Sign.positive => sorry
  | Sign.negative, Sign.negative => sorry
  | Sign.positive, Sign.negative => sorry
  | Sign.negative, Sign.positive => sorry

-- theorem Integer.mul_lhs_neg (a b: Integer) (h1: a.sign = Sign.negative) (h2: b.sign = Sign.positive):
--   (a * b).sign = Sign.negative ∨ (a * b) = 0
-- := by
--   change (mul _ _).sign = Sign.negative ∨ (a * b) = 0
--   unfold mul
--   rw [h1, h2]
--   simp
--   suffices (if a.abs * b.abs <= 0 then Sign.positive else Sign.negative) = Sign.negative ∨ (a * b) = 0 by assumption
--   sorry
--   -- suffices ¬(a.abs * b.abs <= 0) by exact if_neg this
--   -- intro h3
--   -- have l: a.abs * b.abs = 0 := Natural.eq_zero_of_le_zero h3
--   -- cases a using Quot.ind with
--   -- | mk a2 => {
--   --   have d : (if a2.fst <= a2.snd then Sign.positive else Sign.negative) = Sign.negative := h1
--   --   have d : ¬(a2.fst <= a2.snd) := by intro hc; rw [if_pos hc] at d; contradiction;
--   --   -- obtain ⟨c, ht⟩ := (Natural.gt_of_not_le d)
--   --   -- replace l := l.symm
--   --   -- have : ∀a b: Natural, 0 = a * b → a = 0 ∧ b = 0 := by exact?
--   --   -- have h3 : abs (Quot.mk Setoid.r a2) = 0 := by exact?
--   --   sorry
--   -- }

--   -- rw [if_pos (Natural.zero_le _)]

theorem Integer.mul_neg (a b: Integer) (h1: a.sign = Sign.negative) (h2: b.sign = Sign.negative):
  (a * b).sign = Sign.positive
:= by
  change (mul _ _).sign = Sign.positive
  unfold mul
  rw [h1, h2]
  suffices (if 0 <= a.abs * b.abs then Sign.positive else Sign.negative) = Sign.positive by assumption
  rw [if_pos]
  exact Natural.greater_than.equal.zero _

theorem Integer.mul_lt_zero (a b: Integer) (h1: (a * b).sign = Sign.positive):
  a.sign = b.sign
:= by
  sorry

  -- let ab := Integer.mk a.abs * b.abs
  -- cases ab using Quotient.ind

  -- cases a using Quotient.ind
  -- cases b using Quotient.ind
  -- rename_i a b
  -- unfold sign at |- h1 h2

  -- have h1: a.fst <= a.snd := by
  --   cases Natural.lt_trichotomy a.fst a.snd with
  --   | inl hp => exact Natural.le_of_succ_le hp
  --   | inr hp => cases hp with
  --     | inl hp => exact Natural.le_of_eq hp
  --     | inr hp => {
  --       have n: ¬(a.fst <= a.snd) := by exact Natural.not_le_of_lt hp;
  --       have h1: (if a.fst ≤ a.snd then Sign.positive else Sign.negative) = Sign.positive := h1
  --       rw [if_neg n] at h1
  --       contradiction
  --     }

  -- have h2: b.fst <= b.snd := by
  --   cases Natural.lt_trichotomy b.fst b.snd with
  --   | inl hp => exact Natural.le_of_succ_le hp
  --   | inr hp => cases hp with
  --     | inl hp => exact Natural.le_of_eq hp
  --     | inr hp => {
  --       have n: ¬(b.fst <= b.snd) := by exact Natural.not_le_of_lt hp;
  --       have h1: (if b.fst ≤ b.snd then Sign.positive else Sign.negative) = Sign.positive := h2
  --       rw [if_neg n] at h1
  --       contradiction
  --     }

theorem mul_cancel {n m k : Integer} (h1: n * m = n * k): m = k := by
  cases n using Quotient.ind
  cases m using Quotient.ind
  cases k using Quotient.ind
  rename_i a b c
  let (a1, a2) := a
  let (b1, b2) := b
  let (c1, c2) := c
  -- replace h1 := Quotient.exact h1
  sorry

  -- apply Quotient.sound
  -- change _ = _ at h1 |-
  -- ac_nf at h1 |-

-- Needs distribtivity
-- theorem fermat_factorisation (a b: Integer): a * a - b * b = (a + b) * (a - b) := sorry
