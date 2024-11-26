import Mathematics.Algebra.Group
import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication

def Group.power {T: Type} [Group T] (a: T) (n: Natural) : T := match n with
| Natural.zero => 1
| Natural.successor n => (Group.power a n) * a

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
  | zero => rw [power.zero, groups.one.multiply, groups.multiply.one]
  | successor n ih => rw [power.successor, Group.associativity, multiply.right_cancel_iff, ih]

theorem power.one : a ^ (1: Natural) = a := by
  rw [←successor.zero_eq_one, power.successor, power.zero, groups.one.multiply]

theorem one.power (n: Natural) : (1 : T) ^ n = 1 := by
  induction n with
  | zero => exact power.zero 1
  | successor n ih => rw [power.successor, ih, groups.multiply.one]

theorem power.add (m n : Natural) : a ^ (m + n) = a^m * a^n := by
  induction n with
  | zero => rw [Natural.zero_def, Natural.add.zero, ←Natural.zero_def, power.zero, groups.multiply.one]
  | successor n ih => rw [add.successor, power.successor, power.successor, groups.multiply.associative, multiply.right_cancel_iff, ih]

theorem power.multiply (m n : Natural) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Natural.zero_def, multiply.zero, ←Natural.zero_def, power.zero, power.zero]
  | successor n ih => rw [power.successor, ←ih, ←power.add, multiply.successor]

theorem multiply.power {U : Type} [AbelianGroup U] (a b: U) (n : Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [power.zero, power.zero, power.zero, groups.multiply.one]
  | successor n ih => {
    rw [power.successor,
      power.successor,
      power.successor,
      ←groups.multiply.associative (a ^ n) a,
      AbelianGroup.commutativity a (b ^ n * b),
      ih,
      AbelianGroup.commutativity a b,
      ←groups.multiply.associative (b ^ n) b a,
      groups.multiply.associative,
      groups.multiply.associative,
      groups.multiply.associative
    ]
  }

end group_exponents
