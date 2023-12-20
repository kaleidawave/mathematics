import Mathematics.Algebra.Groups
import Mathematics.Structures.Naturals

def Group.pow {T: Type} [Group T] (a: T) (n: Natural) : T := match n with
| Natural.zero => 1
| Natural.successor n => (pow a n) * a

instance {T: Type} [Group T] : Pow T Natural where
  pow := Group.pow

namespace group_exponents

open groups

variable {T: Type} [Group T] (a: T)

theorem pow.zero : a ^ Natural.zero = 1 := rfl

theorem pow.successor (n: Natural) : a ^ Natural.successor n = a ^ n * a := rfl

theorem pow.successor' (n: Natural) : a ^ Natural.successor n = a * a ^ n := by
  rw [pow.successor]
  induction n with
  | zero => rw [pow.zero, one.mul, mul.one]
  | successor n ih => rw [pow.successor, Group.associativity, mul.right_cancel_iff, ih]

theorem pow.one : a ^ (1: Natural) = a := by
  rw [←successor.zero_eq_one, pow.successor, pow.zero, one.mul]

theorem one.pow (n: Natural) : (1 : T) ^ n = 1 := by
  induction n with
  | zero => exact pow.zero 1
  | successor n ih => rw [pow.successor, ih, mul.one]

open addition in
theorem pow.add (m n : Natural) : a ^ (m + n) = a^m * a^n := by
  induction n with
  | zero => rw [zero.eq_zero, add.zero, ←zero.eq_zero, pow.zero, mul.one]
  | successor n ih => rw [add.successor, pow.successor, pow.successor, mul.assoc, mul.right_cancel_iff, ih]

open multiplication in
theorem pow.mul (m n : Natural) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [zero.eq_zero, mul.zero, ←zero.eq_zero, pow.zero, pow.zero]
  | successor n ih => rw [pow.successor, ←ih, ←pow.add, mul.successor]

theorem mul.pow {U : Type} [AbelianGroup U] (a b: U) (n : Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [pow.zero, pow.zero, pow.zero, mul.one]
  | successor n ih => {
    rw [pow.successor,
      pow.successor,
      pow.successor,
      ←mul.assoc (a ^ n) a,
      AbelianGroup.commutativity a (b ^ n * b),
      ih,
      AbelianGroup.commutativity a b,
      ←mul.assoc (b ^ n) b a,
      mul.assoc,
      mul.assoc,
      mul.assoc
    ]
  }

end group_exponents
