import Mathematics.Algebra.Groups
import Mathematics.Structures.Naturals
import Mathematics.Proofs.Logic

-- Having some problems with the below so skipping for now

inductive Integer : Type
| non_negative (n: Natural)
| negative_successor (n: Natural)
deriving Repr

instance (n: Nat): OfNat Integer n := ⟨.non_negative (OfNat.ofNat n)⟩

def Integer.negative : Integer → Integer
| non_negative (Natural.successor n) => .non_negative n
| non_negative zero => .non_negative zero
| negative_successor n => .non_negative (Natural.successor n)

instance : Neg Integer := ⟨Integer.negative⟩

-- TODO think is correct
def Integer.add : Integer → Integer → Integer
| l, 0 => l
| 0, r => r.negative
| non_negative n, non_negative m => .non_negative (n + m)
| negative_successor (Natural.zero), non_negative (Natural.successor n) => .non_negative n
| negative_successor (Natural.successor n), non_negative (Natural.successor m) => (Integer.negative_successor n).add (Integer.non_negative m)
| non_negative (Natural.successor n), negative_successor Natural.zero => .non_negative n
| non_negative (Natural.successor n), negative_successor (Natural.successor m) => (Integer.non_negative n).add (Integer.negative_successor m)
| negative_successor n, negative_successor m => .negative_successor (Natural.successor n + m)

instance : Add Integer := ⟨Integer.add⟩

instance : Coe Natural Integer := ⟨.non_negative⟩

def Integer.sub : Integer → Integer → Integer := fun a b => a + (-b)
instance : Sub Integer := ⟨Integer.sub⟩

@[simp]
theorem Integer.zero_eq_zero : 0 = Integer.non_negative (Natural.zero) := rfl

namespace theorems

variable (m: Integer)

-- theorem add_zero' (n: Natural): Integer.non_negative n + .non_negative .zero = .non_negative n := by
--   cases n
--   rfl
--   rw [←Integer.zero_eq_zero]

end theorems

namespace integer2

-- Subtype based
structure Integer2 where
  right: Natural
  left: Natural
  condition: right = .zero ∨ left = .zero

instance (n: Nat): OfNat Integer2 n := ⟨Integer2.mk (OfNat.ofNat n) 0 (Or.inr rfl)⟩

def Integer2.negative (on: Integer2) : Integer2 := Integer2.mk on.left on.right (Or.symmetric ▸ on.condition)
instance : Neg Integer2 := ⟨Integer2.negative⟩

def normalize : (Natural × Natural) → Integer2
| (.successor n, .successor m) => normalize (n, m)
| (.successor n, .zero) => Integer2.mk (.successor n) .zero (Or.inr rfl)
| (.zero, .successor m) => Integer2.mk .zero (.successor m) (Or.inl rfl)
| (.zero, .zero) => Integer2.mk .zero .zero (Or.inl rfl)

-- theorem normalize.left_zero' (m: Natural) : normalize (.zero, .successor m) = Integer2.mk .zero (.successor m) (Or.inl rfl) := rfl

local instance : Coe (Natural × Natural) Integer2 := ⟨normalize⟩

def Integer2.add (left right: Integer2) : Integer2 := (left.left + right.left, left.right + right.right)

instance : Add Integer2 := ⟨Integer2.add⟩
instance : Sub Integer2 := ⟨fun a b => a + (-b)⟩
instance : Coe Natural Integer2 := ⟨fun n => Integer2.mk n 0 (Or.inr rfl)⟩

theorem Integer2.add.def (left right: Integer2) : left + right = (left.left + right.left, left.right + right.right) := rfl

theorem Integer2.zero.def : (0: Integer2) = ⟨0, 0, (Or.inr rfl)⟩ := rfl

theorem normalize.right_zero : normalize (.zero, .zero) = Integer2.mk .zero .zero (Or.inr rfl) := rfl
theorem normalize.right_zero' (a: Natural) : normalize (.successor a, .zero) = Integer2.mk (.successor a) .zero (Or.inr rfl) := rfl

theorem normalize.right_zero'' (a: Natural) : normalize (a, .zero) = Integer2.mk a .zero (Or.inr rfl) := by
  cases a with
  | zero => exact normalize.right_zero
  | successor n => exact normalize.right_zero' n


theorem normalize.left_zero'' (a: Natural) : normalize (a, .zero) = Integer2.mk a .zero (Or.inr rfl) := by
  cases a with
  | zero => exact normalize.right_zero
  | successor n => exact normalize.right_zero' n

-- theorem normalize.either_zero (a b: Natural) (h: a = 0 ∨ b = 0) : normalize (a, b) = Integer2.mk a b h := by
--   induction b with
--   | zero => exact normalize.right_zero'' a
--   | successor b ih => induction a with
--     | zero => sorry

-- def Integer2.sub : Integer2 → Integer2 → Integer2 := fun a b => a + (-b)

namespace theorems

theorem zero.eq_zero : 0 = Integer2.mk 0 0 (Or.inl rfl) := rfl

-- theorem add_zero' (n: Integer2) : n + 0 = n := by
--   rw [Integer2.zero.def, Integer2.add.def]
--   simp
--   rw [addition.add_zero n.left, addition.add_zero n.right]
--   rfl

end theorems

end integer2
