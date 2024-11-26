import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication

def Natural.power : Natural → Natural → Natural
| _, 0 => 1
| a, (successor b) => (power a b) * a

instance : Pow Natural Natural := ⟨Natural.power⟩

theorem power.zero (n: Natural) : n ^ (0: Natural) = 1 := rfl
theorem power.successor (m n: Natural) : n ^ m.successor = n ^ m * n := rfl

theorem power.one (n: Natural) : n ^ (1: Natural) = n := by
  rw [←successor.zero_eq_one, power.successor, Natural.zero_def, power.zero, one.multiply]

theorem zero.power (n: Natural) (h: n ≠ 0): (0: Natural) ^ n = 0 := by
  cases n with
  | zero => contradiction
  | successor n => rw [power.successor, multiply.zero]

theorem one.power (n: Natural) : (1: Natural) ^ n = 1 := by
  induction n with
  | zero => exact power.zero 1
  | successor n ih => rw [power.successor, multiply.one, ih]

theorem power.add (n a b: Natural) : n ^ (a + b) = n ^ a * n ^ b := by
  induction a with
  | zero => rw [Natural.zero_def, Natural.zero.add, power.zero, one.multiply]
  | successor a ih => rw [successor.add, power.successor, power.successor, ih, multiply.associative, multiply.commutative _ n, multiply.associative]

-- TODO simpler ?
theorem multiply.power (n a b: Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Natural.zero_def, power.zero, power.zero, power.zero, multiply.one]
  | successor n ih => {
    repeat rw [power.successor];
    rw [
      ih,
      multiply.associative,
      multiply.associative,
      multiply.commutative (b ^ n),
      multiply.commutative (b ^ n),
      multiply.associative,
    ]
  }

theorem power.multiply (n a b: Natural) : n ^ (a * b) = (n ^ a) ^ b := by
  induction a with
  | zero => rw [Natural.zero_def, zero.multiply, power.zero, one.power]
  | successor a ih => rw [successor.multiply, power.add, power.successor, ih, multiply.power]

namespace x
  theorem power_def (a b: Natural) : a ^ b = a.power b := rfl

  theorem power.square (a: Natural) : a ^ (2: Natural) = a * a := rfl

  theorem expand.polynomial (a b: Natural) : (a + b) ^ (2: Natural) = a ^ (2: Natural) + 2 * a * b + b ^ (2: Natural) := by
    rw [
      power.square,
      power.square,
      power.square,
      multiply.distributive,
      multiply.distributive.right,
      multiply.commutative 2 a,
      multiply.two,
      multiply.distributive.right,
      multiply.distributive.right,
      Natural.add.associative,
      Natural.add.associative,
      multiply.commutative a b,
    ]

end x
