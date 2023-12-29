import Mathematics.Structures.Numbers.Natural

def Sequence (T: Type) : Type := Natural → T

def s1.a : Sequence Natural
| .zero => .zero
| .successor n => 2 * (s1.a n) + 1

open multiplication addition exponentiation in
example (n: Natural) : (s1.a n) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | successor n nih => {
    unfold s1.a
    rw [
      power.successor,
      ←nih,
      multiply.commutative (s1.a n + 1) _,
      multiply.distributive,
      multiply.one,
      ←add.associative _ 1 1
    ]; rfl
  }

def Sequence.linear (s: Sequence Natural) : Prop := ∃m: Natural, ∀n: Natural, s n + m = s (n + 1)

def s2.a : Sequence Natural := fun n => n * 2

-- Slight excuse to use conv mode
open multiplication.multiply in example : s2.a.linear := ⟨
  2,
  fun n => by
    unfold s2.a;
    conv => rhs; rw [commutative, add, one, commutative]; rfl;
⟩
