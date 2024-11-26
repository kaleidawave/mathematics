import Mathematics.Logic
import Mathematics.Algebra.Group
import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.SaturatingSubtraction
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Inequality

def reduce : Natural → Natural → Natural × Natural
  | 0, n => (0, n)
  | .successor n1, 0 => (.successor n1, 0)
  | .successor n1, .successor n2 => reduce n1 n2

theorem reduce.is_zero (n m: Natural) : (reduce n m).fst = 0 ∨ (reduce n m).snd = 0 := by
  induction n generalizing m with
  | zero => exact (Or.inl rfl)
  | successor n ih1 => cases m with | zero => exact Or.inr rfl | successor m => exact ih1 m

theorem reduce.zero_right (a : Natural) : reduce a 0 = (a, 0) := by cases a <;> rfl
theorem reduce.zero_left (a : Natural) : reduce 0 a = (0, a) := by cases a <;> rfl

def Prod.swap {T U: Type}: Prod T U → Prod U T := fun (l, r) => (r, l)

theorem reduce.swap (a b : Natural) : Prod.swap (reduce a b) = reduce b a := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | successor _ ih =>
    cases b
    · rfl
    · unfold reduce
      rw [ih]

theorem reduce.successor_successor (n m: Natural) : reduce n.successor m.successor = reduce n m := rfl

theorem reduce.self (n: Natural) : reduce n n = (0, 0) := by
  induction n with
  | zero => rfl
  | successor n ih => exact reduce.successor_successor n n ▸ ih

theorem reduce.succ (n: Natural) : reduce (n.successor) n = (1, 0) := by
  induction n with
  | zero => rfl
  | successor n ih => exact reduce.successor_successor _ _ ▸ ih

theorem reduce_add_add (a b k : Natural) : reduce (a + k) (b + k) = reduce a b := by
  induction k with
  | zero => rw [Natural.zero_def, Natural.add.zero, Natural.add.zero];
  | successor _ ih => rwa [add.successor, add.successor, reduce.successor_successor]

theorem reduce_of_le (a b : Natural) (h : a <= b) : reduce a b = (0, b -ˢ a) := by
  obtain ⟨k, rfl⟩ := h
  have := reduce_add_add 0 k a
  rw [Natural.zero.add, Natural.add.commutative k] at this
  rw [this, reduce.zero_left, add_sub_cancel_left]

theorem reduce_of_ge (a b : Natural) (h : b <= a) : reduce a b = (a -ˢ b, 0) := by
  rw [←reduce.swap, reduce_of_le _ _ h, Prod.swap]

theorem reduce.left_inj (a b c : Natural) (h : reduce a b = reduce a c) : b = c := by
  obtain hb | hb := Natural.le_total a b
    <;> obtain hc | hc := Natural.le_total a c
    <;> simp [reduce_of_le, reduce_of_ge, hb, hc] at h
    <;> sorry

-- LFG!!!
theorem reduce_eq_iff (a b a' b' : Natural) : reduce a b = reduce a' b' ↔ a + b' = b + a' := by
  obtain h1 | h1 := Natural.le_total a b
    <;> obtain h2 | h2 := Natural.le_total a' b'
    <;> simp [reduce_of_le, reduce_of_ge, h1, h2]
    <;> sorry

-- theorem reduce_add (a b : Natural): a + (reduce a b).snd = b + (reduce a b).fst := by
--   induction a
--   case zero => simp [reduce]
--   case successor a ih =>
--     cases b
--     case zero => simp [reduce]
--     case successo b =>
--       simp [reduce]
--       rw [add_comm a 1, add_assoc 1 a, ih b]
--       rw [← add_assoc 1 b, add_comm b 1]

  -- obtain h1 | h1 := Natural.le_total a b;
  -- obtain h2 | h2 := Natural.le_total a' b';
  -- rw [reduce_of_le, reduce_of_le];
  -- exact ⟨by intro h3; , by intro h1⟩
  -- sorry
  -- obtain
  --   <;>
  --   <;> simp [reduce_of_le, reduce_of_ge, h1, h2]
  --   <;> omega

def Integer := { integer: Prod Natural Natural // integer.fst = 0 ∨ integer.snd = 0 }

@[reducible]
def Integer.is_positive (self: Integer) : Prop := self.val.snd = 0

instance : Coe Natural Integer where
  coe n := Subtype.mk { fst := n, snd := 0 } (Or.inr rfl)

instance : Coe Integer Int where
  coe n := if Integer.is_positive n then Int.ofNat (Natural.to.nat n.val.fst) else Int.negOfNat (Natural.to.nat n.val.snd)

instance (n : Nat) : OfNat Integer n where
  ofNat := Natural.from.nat n

instance : Repr Integer where
  reprPrec := fun n m => Repr.reprPrec (↑n: Int) m

def Integer.absolute (self: Integer) : Natural := if self.val.fst = 0 then self.val.snd else self.val.fst

-- #eval Integer.absolute (Integer.negate 4)
-- #eval -(4: Integer)
-- #eval (7: Integer) + (-5: Integer)
-- #eval (7: Integer) - (-5: Integer)

-- example : (⟨2, 1⟩: Integer) = (⟨4, 3⟩: Integer) := by rfl
-- #eval OfNat Natural 2
