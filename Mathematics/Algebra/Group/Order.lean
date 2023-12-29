import Mathematics.Algebra.Group
import Mathematics.Structures.Numbers.Natural

def Group.power {T: Type} [Group T] (a: T) (n: Natural) : T := match n with
| Natural.zero => 1
| Natural.successor n => (pow a n) * a

instance {T: Type} [Group T] : Pow T Natural where
  pow := Group.power

namespace group_exponents

open groups

variable {T: Type} [Group T] (a: T)

theorem power.zero : a ^ Natural.zero = 1 := rfl

theorem power.successor (n: Natural) : a ^ Natural.successor n = a ^ n * a := rfl

theorem power.successor' (n: Natural) : a ^ Natural.successor n = a * a ^ n := by
  rw [power.successor]
  induction n with
  | zero => rw [power.zero, one.multiply, multiply.one]
  | successor n ih => rw [power.successor, Group.associativity, multiply.right_cancel_iff, ih]

theorem power.one : a ^ (1: Natural) = a := by
  rw [←successor.zero_eq_one, power.successor, power.zero, one.multiply]

theorem one.power (n: Natural) : (1 : T) ^ n = 1 := by
  induction n with
  | zero => exact power.zero 1
  | successor n ih => rw [power.successor, ih, multiply.one]

open addition in
theorem power.add (m n : Natural) : a ^ (m + n) = a^m * a^n := by
  induction n with
  | zero => rw [zero.eq_zero, add.zero, ←zero.eq_zero, power.zero, multiply.one]
  | successor n ih => rw [add.successor, power.successor, power.successor, multiply.associative, multiply.right_cancel_iff, ih]

open multiplication in
theorem power.multiply (m n : Natural) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [zero.eq_zero, multiply.zero, ←zero.eq_zero, power.zero, power.zero]
  | successor n ih => rw [power.successor, ←ih, ←power.add, multiply.successor]

theorem multiply.power {U : Type} [AbelianGroup U] (a b: U) (n : Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [power.zero, power.zero, power.zero, multiply.one]
  | successor n ih => {
    rw [power.successor,
      power.successor,
      power.successor,
      ←multiply.associative (a ^ n) a,
      AbelianGroup.commutativity a (b ^ n * b),
      ih,
      AbelianGroup.commutativity a b,
      ←multiply.associative (b ^ n) b a,
      multiply.associative,
      multiply.associative,
      multiply.associative
    ]
  }

end group_exponents
