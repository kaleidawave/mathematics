-- Will be split up into files. TODO namespacing

import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Subtraction
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Ordering
import Mathematics.Structures.Numbers.Natural.Multiplication

def NatPair : Type := Natural × Natural

instance : Coe NatPair (Natural × Natural) := ⟨id⟩
instance : Coe (Natural × Natural) NatPair := ⟨id⟩

@[reducible, simp]
def PairEq : NatPair → NatPair → Prop := fun (b, a) (d, c) => a + d = c + b

def PairEq.equivalence : Equivalence PairEq where
  refl := by intro x; rfl
  symm := by
    intro x y h1
    exact h1.symm
  trans := by
    intro x y z h1 h2
    have add_eq {a b c d: Natural} (h1: a = b) (h2: c = d) : a + c = b + d := by rw [h1, h2]
    have h3 := add_eq h1 h2
    suffices y.fst + y.snd + _ = y.fst + y.snd + _ from add.left_cancel (x.snd + z.fst) _ _ |>.mp this
    ac_nf at h3 |-
    -- rw [ add.commutative y.snd x.fst, add.commutative z.snd y.fst, ←add.associative, ←add.associative, add.associative x.snd, add.commutative y.fst y.snd, add.associative x.fst, add.associative x.fst, add.commutative _ z.snd, ←add.associative, add.associative _ y.snd _, add.associative, add.commutative _ z.fst, ←add.associative, ←add.associative x.fst, add.commutative x.fst ] at h3

instance : Setoid NatPair where
  r := PairEq
  iseqv := PairEq.equivalence

def Setoid.NatPair : Setoid NatPair := inferInstance

@[reducible]
def Integer : Type := Quotient (Setoid.NatPair)

-- instance : Repr Integer where
  -- reprPrec := fun int n => int.lift (fun x => reprPrec (x.1, x.2) n) (by intro x y c; simp; rfl)

def Integer.mk (a: Natural × Natural) : Integer := Quot.mk PairEq a

instance (p q : NatPair) : Decidable (p ≈ q) := match p, q with
  | (a, b), (c, d) => inferInstanceAs <| Decidable (PairEq (a, b) (c, d))

instance : DecidableEq Integer := inferInstanceAs <| DecidableEq (Quotient Setoid.NatPair)

@[reducible]
def Integer.from.nat : Nat -> Integer := fun n => Integer.mk (0, Natural.from.nat n)

-- @[reducible]
-- def Natural.to.nat : Natural -> Nat
-- | Natural.zero => .zero
-- | Natural.successor n => Natural.succ (Natural.to.nat n)

instance (n: Nat) : OfNat Integer n where
  ofNat := Integer.from.nat n

def Integer.zero := Integer.mk (0, 0)

instance : Zero Integer := ⟨Integer.zero⟩

-- def Integer.id (int: Integer): Integer := Quotient.lift
--   (fun p: NatPair => Integer.mk (p.1, p.2))
--   (by intro x y h1; apply Quotient.sound; exact h1)
--   int

def Integer.neg (int: Integer): Integer := Quotient.lift
  (fun p: NatPair => Integer.mk (p.2, p.1))
  (by
    intro x y h1
    have d: x.snd + y.fst = y.snd + x.fst := h1
    apply Quotient.sound
    change PairEq (x.snd, x.fst) (y.snd, y.fst)
    simp
    rw [add.commutative x.fst, add.commutative y.fst]
    exact d.symm
  ) int

instance : Neg Integer := ⟨Integer.neg⟩

theorem Integer.neg.neg (n: Integer) : -(-n) = n := by
  cases n using Quotient.ind
  apply Quotient.sound
  rfl

def Integer.add (a b: Integer): Integer := Quotient.lift₂
  (fun a b: NatPair => Integer.mk (a.fst + b.fst, a.snd + b.snd))
  (by
    intro (a, b) (c, d) (e, f) (g, h) h1 h2
    replace h1 : b + e = f + a := h1
    replace h2 : d + g = h + c := h2
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    -- TODO via calc
    conv => lhs; rw [
      ←add.associative,
      add.commutative b,
      add.associative d,
      h1,
      add.commutative _ g,
      add.commutative f,
    ]
    conv => rhs; rw [
      add.associative,
      add.commutative a,
      ←add.associative h,
      ←h2,
      add.commutative d,
      add.commutative f
    ]
    rw [←add.associative, ←add.associative]
  ) a b

instance : Add Integer := ⟨Integer.add⟩

theorem Integer.add.zero (a: Integer) : a + 0 = a := by
  cases a using Quotient.ind
  apply Quotient.sound
  have d : Natural.from.nat 0 = 0 := rfl
  rw [Natural.add.zero, d, Natural.add.zero]
  rfl

-- Namespace collision
def nat_add_zero : ∀a: Natural, a + 0 = a := Natural.add.zero
def nat_zero_add : ∀a: Natural, 0 + a = a := zero.add
def nat_add_comm : ∀a b: Natural, a + b = b + a := add.commutative
def nat_add_assoc : ∀a b c: Natural, (a + b) + c = a + (b + c) := add.associative

theorem Integer.add.commutative (a b: Integer) : a + b = b + a := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound
  rw [nat_add_comm]
  conv => rhs; rhs; rw [nat_add_comm]
  rfl

theorem Integer.add.associative (a b: Integer) : a + (b + c) = (a + b) + c := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  cases c using Quotient.ind
  apply Quotient.sound
  rw [nat_add_assoc, nat_add_assoc]
  rfl

def Integer.sub (a b: Integer): Integer := a + b.neg

instance : Sub Integer := ⟨Integer.sub⟩

theorem Integer.sub.self (a: Integer) : a - a = 0 := by
  cases a using Quotient.ind
  apply Quotient.sound
  change PairEq _ _
  rename_i a
  let (a, b) := a
  simp
  rw [Natural.add.zero, zero.add, nat_add_comm]

theorem Integer.sub.zero (a: Integer) : a - 0 = a := by
  cases a using Quotient.ind
  apply Quotient.sound
  change PairEq _ _
  rename_i a
  let (a, b) := a
  unfold PairEq
  simp
  rw [Natural.add.zero, Natural.add.zero]

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

inductive Polarity : Type | positive | negative deriving BEq

theorem Polarity.binary_relation (p1 p2: Polarity): p1 == p2 ∨ p1 != p2 := by
  match p1, p2 with
  | Polarity.positive, Polarity.positive => left; rfl
  | Polarity.negative, Polarity.negative => left; rfl
  | Polarity.positive, Polarity.negative => right; rfl
  | Polarity.negative, Polarity.positive => right; rfl

theorem Polarity.neq {p1 p2: Polarity} (h1: p1 != p2): ¬(p1 == p2) := by
  match p1, p2 with
  | Polarity.positive, Polarity.positive => contradiction
  | Polarity.negative, Polarity.negative => contradiction
  | Polarity.positive, Polarity.negative => simp; rfl
  | Polarity.negative, Polarity.positive => simp; rfl

instance : PartialEquivBEq Polarity where
  symm := by
    intro p1 p2 h1;
    cases p1
    cases p2; rfl; contradiction
    cases p2; contradiction; rfl;
  trans := by
    intro p1 p2 p3 h1 h2;
    cases p1;
    cases p2; exact h2; contradiction;
    cases p2; contradiction; exact h2;

theorem Polarity.neq_comm {p1 p2: Polarity}: (p1 != p2) = (p2 != p1) := bne_comm
theorem Polarity.comm {p1 p2: Polarity}: (p1 == p2) = (p2 == p1) := BEq.comm

theorem polarity_ne: Polarity.positive ≠ Polarity.negative := by intro h1; contradiction;

def Integer.polarity (Integer: Integer): Polarity := Quotient.liftOn
  Integer
  (fun (a, b) => if a <= b then Polarity.positive else Polarity.negative)
  (by
    intro (a, b) (c, d) pair_eq
    change PairEq (a, b) (c, d) at pair_eq
    unfold PairEq at pair_eq
    simp at pair_eq |-

    cases Natural.lt_trichotomy a b with
    | inl h1 => {
      have h3 : a <= b := Natural.less_than_implies_less_than_equal h1
      obtain ⟨l, h1⟩ := h3
      rw [←h1, nat_add_comm d, nat_add_assoc, add.left_cancel, nat_add_comm] at pair_eq
      rw [if_pos ⟨l, h1⟩, if_pos ⟨l, pair_eq⟩]
    }
    | inr h1 => cases h1 with
    | inl h1 => {
      rw [h1] at |- pair_eq
      rw [nat_add_comm d, add.left_cancel] at pair_eq
      have b_lt: b <= b := Natural.less_than.equal.self _
      have c_lt: c <= d := pair_eq ▸ (Natural.less_than.equal.self _)
      rw [if_pos b_lt, if_pos c_lt]
    }
    | inr h1 => {
      have ⟨l, bd⟩ := h1
      rw [
        ←bd,
        successor.add, ←add.successor,
        ←nat_add_assoc, nat_add_comm _ b, nat_add_assoc, add.left_cancel,
        add.successor, ←successor.add
      ] at pair_eq
      have h2: c > d := ⟨l, pair_eq.symm⟩
      have h1: ¬(a <= b) := Natural.less_than_not_greater_than h1
      have h2: ¬(c <= d) := Natural.less_than_not_greater_than h2
      rw [if_neg h1, if_neg h2]
    }
  )

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
        rw [←h1n, nat_add_comm d, nat_add_assoc, add.left_cancel, nat_add_comm] at pair_eq
        exists n
      rw [
        if_pos h1,
        if_pos h2,
        subtraction_eq_iff_eq_add h1,
        nat_add_comm,
        -- ←Natural.Simproc.add_eq_add_le b a h2,
        -- nat_add_comm a
      ]
      sorry
      -- exact pair_eq
    }
    | inr h1 => cases h1 with
    | inl h1 => {
      rw [h1] at |- pair_eq
      rw [nat_add_comm d, add.left_cancel] at pair_eq
      have b_lt: b <= b := Natural.less_than.equal.self b
      have c_lt: c <= d := pair_eq ▸ (Natural.less_than.equal.self _)
      rw [if_pos b_lt, if_pos c_lt, pair_eq, subtraction.self, subtraction.self]
    }
    | inr h1 => {
      have ⟨l, bd⟩ := h1
      rw [
        ←bd,
        successor.add, ←add.successor, ←nat_add_assoc, nat_add_comm _ b, nat_add_assoc,
        add.left_cancel, add.successor, ←successor.add
      ] at pair_eq
      have h2: c > d := ⟨l, pair_eq.symm⟩
      have h1: ¬(a <= b) := Natural.less_than_not_greater_than h1
      have h2: ¬(c <= d) := Natural.less_than_not_greater_than h2
      rw [if_neg h1, if_neg h2]
      rw [pair_eq, ←bd, nat_add_comm, nat_add_comm _ l]
      rw [add.successor, ←successor.add, subtraction.lhs.addition]
      rw [add.successor, ←successor.add, subtraction.lhs.addition]
    }
  )

def Integer.mul (a b: Integer): Integer := match a.polarity, b.polarity with
| Polarity.positive, Polarity.positive => Integer.mk (0, a.abs * b.abs)
| Polarity.negative, Polarity.negative => Integer.mk (0, a.abs * b.abs)
| Polarity.positive, Polarity.negative => Integer.mk (a.abs * b.abs, 0)
| Polarity.negative, Polarity.positive => Integer.mk (a.abs * b.abs, 0)

def Integer.mul2 (a b: Integer): Integer := if
  a.polarity == b.polarity
  then Integer.mk (0, a.abs * b.abs)
  else Integer.mk (a.abs * b.abs, 0)

theorem MulEqDev (a b: Integer): Integer.mul a b = Integer.mul2 a b := by
  unfold Integer.mul Integer.mul2
  match a.polarity, b.polarity with
  | Polarity.positive, Polarity.positive => rw [if_pos]; rfl
  | Polarity.negative, Polarity.negative => rw [if_pos]; rfl
  | Polarity.positive, Polarity.negative => rw [if_neg]; exact Polarity.neq rfl
  | Polarity.negative, Polarity.positive => rw [if_neg]; exact Polarity.neq rfl

instance : Mul Integer := ⟨Integer.mul⟩

theorem Integer.mul_comm (a b: Integer): a * b = b * a := by
  change Integer.mul _ _ = Integer.mul _ _
  rw [MulEqDev, MulEqDev]
  unfold mul2
  have d : ∀p1 p2: Polarity, p1 = p2 ∨ p1 ≠ p2 := by
    intro p1 p2
    match p1, p2 with
    | Polarity.positive, Polarity.positive => left; rfl
    | Polarity.negative, Polarity.negative => left; rfl
    | Polarity.positive, Polarity.negative => right; exact Polarity.noConfusion
    | Polarity.negative, Polarity.positive => right; exact Polarity.noConfusion

  cases Polarity.binary_relation a.polarity b.polarity with
  | inl h1 => rw [if_pos h1, if_pos <| Polarity.comm ▸ h1]; rw [multiply.commutative];
  | inr h1 => {
    have n1 := Polarity.neq h1
    have n2 := Polarity.neq <| Polarity.neq_comm ▸ h1
    rw [if_neg n1, if_neg n2, multiply.commutative];
  }

#print axioms Integer.mul_comm

theorem Integer.mul_pos (a b: Integer) (h1: a.polarity = Polarity.positive) (h2: b.polarity = Polarity.positive):
  (a * b).polarity = Polarity.positive
:= by
  change (mul _ _).polarity = Polarity.positive
  unfold mul
  rw [h1, h2]
  suffices (if 0 <= a.abs * b.abs then Polarity.positive else Polarity.negative) = Polarity.positive by assumption
  rw [if_pos (Natural.greater_than.equal.zero _)]

#check if_neg

theorem Integer.mk_zero (a: Natural): Integer.mk (a, a) = 0 := by
  apply Quotient.sound
  change PairEq _ _
  unfold PairEq
  exact nat_add_comm a 0

theorem Integer.one (a: Natural): Integer.mk (a, a.successor) = 1 := by
  apply Quotient.sound
  change PairEq _ _
  unfold PairEq
  simp
  rw [successor.add, Natural.add.zero, nat_add_comm, add.one]

theorem Integer.left_right (i: Integer): ∃a: Natural, i = Integer.mk (0, a) ∨ i = Integer.mk (a, 0) := by
  cases i using Quotient.ind
  rename_i p
  let (a, b) := p
  cases Natural.le_total a b
  next h1 =>
    exists b -ₛ a
    -- obtain ⟨c, h2⟩ := h1
    left
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    rw [Natural.add.zero]
    sorry
    -- exact (subtraction.lhs.addition''' _ _).symm
    -- exact (Natural.sub_eq_iff_eq_add h1).mp rfl
  next h1 =>
    exists a -ₛ b
    right
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    rw [nat_add_comm]
    sorry
    -- exact Natural.sub_add_cancel h1

instance NatIntegerCoe : Coe Natural Integer := ⟨fun n => Integer.mk (0, n)⟩

theorem Integer.left_right2 (i: Integer): ∃n: Natural, i = n ∨ i = -n := Integer.left_right i

theorem Integer.abs_zero: (0: Integer).abs = 0 := rfl
theorem Integer.abs_one: (1: Integer).abs = 1 := rfl
theorem Integer.abs_minus_one: (-1: Integer).abs = 1 := rfl

theorem Integer.abs_eq_zero (a: Integer): a.abs = 0 ↔ a = 0 := by
  constructor
  {
    intro h1;
    cases a using Quot.ind with
    | mk a => {
      let (a, b) := a;
      have h2: (if a <= b then b -ₛ a else a -ₛ b) = 0 := h1
      apply Quotient.sound
      split at h2
      case isTrue h1 =>
        change PairEq _ _
        unfold PairEq
        simp
        obtain ⟨c, ht⟩ := h1
        rw [←ht, nat_add_comm, subtraction.lhs.addition] at h2
        rw [h2, nat_add_zero a] at ht
        rw [←ht, nat_add_comm]
        -- exact (h2 ▸ ht).symm
      case isFalse h1 =>
        have h1: a > b := sorry --  Natural.gt_of_not_le h1
        obtain ⟨c, ht⟩ := h1
        rw [←ht, successor.add, ←add.successor, nat_add_comm, subtraction.lhs.addition] at h2
        contradiction
    }
  }
  intro h1; rw [h1]; rfl

theorem Integer.mul_lhs_neg (a b: Integer) (h1: a.polarity = Polarity.negative) (h2: b.polarity = Polarity.positive):
  (a * b).polarity = Polarity.negative ∨ (a * b) = 0
:= by
  change (mul _ _).polarity = Polarity.negative ∨ (a * b) = 0
  unfold mul
  rw [h1, h2]
  simp
  suffices (if a.abs * b.abs <= 0 then Polarity.positive else Polarity.negative) = Polarity.negative ∨ (a * b) = 0 by assumption
  sorry
  -- suffices ¬(a.abs * b.abs <= 0) by exact if_neg this
  -- intro h3
  -- have l: a.abs * b.abs = 0 := Natural.eq_zero_of_le_zero h3
  -- cases a using Quot.ind with
  -- | mk a2 => {
  --   have d : (if a2.fst <= a2.snd then Polarity.positive else Polarity.negative) = Polarity.negative := h1
  --   have d : ¬(a2.fst <= a2.snd) := by intro hc; rw [if_pos hc] at d; contradiction;
  --   -- obtain ⟨c, ht⟩ := (Natural.gt_of_not_le d)
  --   -- replace l := l.symm
  --   -- have : ∀a b: Natural, 0 = a * b → a = 0 ∧ b = 0 := by exact?
  --   -- have h3 : abs (Quot.mk Setoid.r a2) = 0 := by exact?
  --   sorry
  -- }

  -- rw [if_pos (Natural.zero_le _)]

theorem Integer.mul_neg (a b: Integer) (h1: a.polarity = Polarity.negative) (h2: b.polarity = Polarity.negative):
  (a * b).polarity = Polarity.positive
:= by
  change (mul _ _).polarity = Polarity.positive
  unfold mul
  rw [h1, h2]
  suffices (if 0 <= a.abs * b.abs then Polarity.positive else Polarity.negative) = Polarity.positive by assumption
  rw [if_pos]
  exact Natural.greater_than.equal.zero _

theorem Integer.mul_lt_zero (a b: Integer) (h1: (a * b).polarity = Polarity.positive):
  a.polarity = b.polarity
:= by
  sorry

  -- let ab := Integer.mk a.abs * b.abs
  -- cases ab using Quotient.ind

  -- cases a using Quotient.ind
  -- cases b using Quotient.ind
  -- rename_i a b
  -- unfold polarity at |- h1 h2

  -- have h1: a.fst <= a.snd := by
  --   cases Natural.lt_trichotomy a.fst a.snd with
  --   | inl hp => exact Natural.le_of_succ_le hp
  --   | inr hp => cases hp with
  --     | inl hp => exact Natural.le_of_eq hp
  --     | inr hp => {
  --       have n: ¬(a.fst <= a.snd) := by exact Natural.not_le_of_lt hp;
  --       have h1: (if a.fst ≤ a.snd then Polarity.positive else Polarity.negative) = Polarity.positive := h1
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
  --       have h1: (if b.fst ≤ b.snd then Polarity.positive else Polarity.negative) = Polarity.positive := h2
  --       rw [if_neg n] at h1
  --       contradiction
  --     }

theorem if_map {T U: Type} (f: T → U): ∀(c: Bool) (a b: T), (f (if c then a else b)) = if c then f a else f b := fun c a b => apply_ite f (c = true) a b

theorem if_eq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = a): c := by
  split at h2
  assumption
  exact h1 h2.symm |>.elim

theorem if_neq_reduction {T: Type} (c: Prop) [Decidable c] (a b: T) (h1: a ≠ b) (h2: (if c then a else b) = b): ¬c := by
  split at h2
  exact h1 h2 |>.elim
  assumption

theorem X₂ : ∀(c: Bool) (a b: Integer), (if c then a else b).abs = if c then a.abs else b.abs := fun c a b => apply_ite Integer.abs (c = true) a b

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
    have h2 : a = 0 := sorry -- Natural.eq_zero_of_le_zero h1;
    rw [h2];
    exact subtraction.rhs.zero _
  }
  rw [if_neg h1]; rw [subtraction.rhs.zero]

theorem Integer.abs_mul (a b: Integer): (a * b).abs = a.abs * b.abs := by
  conv in (_ * _) => change Integer.mul _ _; unfold mul
  match a.polarity, b.polarity with
  | Polarity.positive, Polarity.positive => rw [Integer.abs_right];
  | Polarity.negative, Polarity.negative => rw [Integer.abs_right];
  | Polarity.negative, Polarity.positive => rw [Integer.abs_left];
  | Polarity.positive, Polarity.negative => rw [Integer.abs_left];

theorem Integer.mul_zero (a: Integer): a * 0 = 0 := by
  change Integer.mul a 0 = _
  unfold mul
  rw [Integer.abs_zero, multiply.zero, Integer.mk_zero];
  split <;> rfl

#eval (-1: Integer).polarity

theorem Integer.mul_minus_one (a: Integer): a * -1 = -a := by
  change Integer.mul a _ = Integer.neg _
  unfold mul
  have h1 : (-1: Integer).polarity = Polarity.negative := rfl
  rw [Integer.abs_minus_one, multiply.one, h1]
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold neg
  sorry

theorem Integer.mul_add (a b c: Integer): a * (b + c) = a * b + a * c := by
  change Integer.mul _ (Integer.add b c) = _
  sorry
  -- unfold mul add

  -- match b.polarity, c.polarity with
  -- | Polarity.positive, Polarity.positive => sorry
  -- | Polarity.negative, Polarity.positive => sorry
  -- | Polarity.negative, Polarity.negative => sorry
  -- | Polarity.positive, Polarity.negative => sorry

def nat_mul_assoc := multiply.associative

theorem Integer.mul_assoc (a b c: Integer): a * (b * c) = (a * b) * c := by
  change Integer.mul _ _ = Integer.mul _ _
  unfold mul
  rw [abs_mul, abs_mul, ←nat_mul_assoc]
  match a.polarity, c.polarity with
  | Polarity.positive, Polarity.positive => sorry
  | Polarity.negative, Polarity.negative => sorry
  | Polarity.positive, Polarity.negative => sorry
  | Polarity.negative, Polarity.positive => sorry

def Integer.to_int (Integer: Integer): Int := Quotient.liftOn
  Integer
  (fun (a, b) => (Int.ofNat <| Natural.to.nat b) - (Int.ofNat <| Natural.to.nat a))
  (by
    intro (a, b) (c, d) h1
    change b + c = d + a at h1
    simp
    refine Int.sub_eq_iff_eq_add'.mpr ?_
    have h2: ∀a b c: Int, (a + (b - c)) = (a + b) - c := by exact fun a b c => Eq.symm (Int.add_sub_assoc a b c)
    rw [h2]
    symm
    refine Int.sub_eq_iff_eq_add'.mpr ?_
    have h3 : ∀a b: Natural, ((Natural.to.nat a + Natural.to.nat b): Int) = ↑(Natural.to.nat a + Natural.to.nat b) := fun _ _ => rfl
    rw [Int.add_comm, Int.add_comm (Natural.to.nat c), h3, h3]
    sorry
  )

def Integer.le (a b: Integer): Prop := Quotient.liftOn₂
  a b
  (fun (b, a) (d, c) => a + d <= c + b)
  (by
    intro (a, b) (c, d) (e, f) (g, h) h1 h2
    change b + e = f + a at h1
    change d + g = h + c at h2
    have add_left : ∀{a b: Natural} (c: Natural), a <= b ↔ a + c <= b + c := by
      intro h1
      sorry
    have add_right : ∀{a b: Natural} (c: Natural), a <= b ↔ c + a <= c + b := by
      intro h1
      sorry
    simp
    constructor
    {
      intro h3
      rw [
        add_left a,
        add_left d,
        nat_add_comm f,
        nat_add_assoc g,
        nat_add_comm,
        ←nat_add_assoc,
        ←h1,
        h2,
        nat_add_assoc,
        nat_add_assoc,
        nat_add_assoc,
        ←add_right,
        ←nat_add_assoc,
        nat_add_comm _ e,
        ←add_right,
        nat_add_comm c,
        nat_add_comm a,
      ]
      exact h3
    }
    {
      intro h3
      rw [
        add_left e,
        add_left h,
        nat_add_comm b,
        nat_add_assoc c,
        nat_add_comm c,
        nat_add_assoc,
        nat_add_comm c,
        h1,
        ←h2,
        nat_add_comm f,
        nat_add_comm d a,
        nat_add_assoc,
        nat_add_assoc,
        nat_add_assoc,
        ←add_right,
        ←nat_add_assoc,
        nat_add_comm f d,
        nat_add_assoc,
        ←add_right,
        nat_add_comm e,
      ]
      exact h3
    }
  )

def Integer.successor (a: Integer): Integer := a + 1

instance : LE Integer := ⟨Integer.le⟩
instance : LT Integer := ⟨fun a b => a.successor <= b⟩

instance (p q : Integer) : Decidable (p <= q) :=
  Quotient.recOnSubsingleton₂ p q (fun (b, a) (d, c) => inferInstanceAs (Decidable (a + d <= c + b)))

#eval (-3: Integer) <= 2
#eval (-3: Integer) <= -6

instance (a b: NatPair) : Decidable (a ≈ b) :=
  inferInstanceAs (Decidable (a.snd + b.fst = b.snd + a.fst))

#eval (-3: Integer) = 2
#eval (-3: Integer) = -6
#eval (-3: Integer) = -3

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
  rw [nat_add_zero]
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
  rw [nat_add_zero] at h1
  simp at h1
  ac_nf at h1 |-

-- def PairEq : NatPair → NatPair → Prop := fun (b, a) (d, c) => a + d = c + b
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
theorem fermat_factorisation (a b: Integer): a * a - b * b = (a + b) * (a - b) := sorry

theorem positive_greater_tham (a: Integer): 0 <= a ↔ a.polarity = Polarity.positive := by
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold Integer.polarity
  constructor
  {
    intro h1
    obtain ⟨c, h2⟩ := le_nat _ _ h1
    replace h2 := Quotient.exact h2
    apply if_pos
    change _ = _ at h2
    simp at h2
    rw [nat_add_zero, nat_zero_add, nat_add_comm, nat_add_zero] at h2
    exists c
  }
  {
    intro h1
    replace h1: (if a ≤ b then Polarity.positive else Polarity.negative) = Polarity.positive := h1
    change 0 + a <= b + 0
    rw [nat_add_zero, nat_zero_add]
    exact if_eq_reduction _ _ _ polarity_ne h1
  }

theorem negative_less_tham (a: Integer): a < 0 ↔ a.polarity = Polarity.negative := by
  cases a using Quotient.ind
  rename_i a
  let (a, b) := a
  unfold Integer.polarity
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
    rw [nat_add_zero, nat_add_zero, nat_add_zero, nat_zero_add] at h2
    rw [←h2, nat_add_assoc, nat_add_assoc] at h3
    conv at h3 => rhs; rw [←nat_add_zero b]
    rw [add.left_cancel, nat_add_comm, add.one] at h3
    contradiction
  }
  {
    intro h1
    have h2: (if a ≤ b then Polarity.positive else Polarity.negative) = Polarity.negative := h1
    change Integer.le _ _
    unfold Integer.le Integer.successor
    rw [←Integer.one a]
    have h3 := if_neq_reduction _ _ _ polarity_ne h2
    change _ + _ <= _ + _
    simp
    rw [nat_add_zero, nat_zero_add]
    sorry
    -- rw [Natural.not_le_eq] at h3
    -- obtain ⟨c2, h3⟩ := h3
    -- rw [Natural.add_succ, ←Natural.succ_add]
    -- apply @Natural.le.intro _ _ c2
    -- rw [Natural.succ_eq_add_one, nat_add_assoc, nat_add_comm a, ←nat_add_assoc, h3]
  }

#check if_neg

theorem tricotomy (a: Integer): a < 0 ∨ a = 0 ∨ a > 0 := by
  cases h1: a.polarity with
  | positive =>
    right;
    have d := positive_greater_tham a |>.mpr h1
    obtain ⟨c, h2⟩ := le_nat 0 a d
    rw [Integer.add.commutative, Integer.add.zero] at h2
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
    exact (negative_less_tham a).mpr h1
  }
