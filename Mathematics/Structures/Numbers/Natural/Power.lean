import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication

def Natural.power : Natural → Natural → Natural
| _, 0 => 1
| a, (successor b) => (power a b) * a

instance : Pow Natural Natural := ⟨Natural.power⟩

theorem Natural.power_zero (n: Natural) : n ^ (0: Natural) = 1 := rfl
theorem Natural.power_successor (m n: Natural) : n ^ m.successor = n ^ m * n := rfl
theorem Natural.power_def (a b: Natural) : a ^ b = a.power b := rfl
theorem Natural.power_one (n: Natural) : n ^ (1: Natural) = n := rfl
theorem Natural.power_two (n: Natural) : n ^ (2: Natural) = n * n := rfl

theorem Natural.zero_power (n: Natural) (h: n ≠ 0): (0: Natural) ^ n = 0 := by
  cases n with
  | zero => contradiction
  | successor n => rw [power_successor, Natural.multiply_zero]

theorem Natural.one_power (n: Natural) : (1: Natural) ^ n = 1 := by
  induction n with
  | zero => exact power_zero 1
  | successor n ih => rw [power_successor, Natural.multiply_one, ih]

theorem Natural.power_add (n a b: Natural) : n ^ (a + b) = n ^ a * n ^ b := by
  induction a with
  | zero => rw [Natural.zero_def, zero_add, power_zero, Natural.one_multiply]
  | successor a ih =>
    rw [successor.add, power_successor, power_successor, ih]
    rw [multiply_associative, multiply_commutative _ n, multiply_associative]

-- TODO simpler ?
theorem Natural.multiply.power (n a b: Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Natural.zero_def, power_zero, power_zero, power_zero, multiply_one]
  | successor n ih => {
    repeat rw [power_successor];
    rw [
      ih,
      multiply_associative,
      multiply_associative,
      multiply_commutative (b ^ n),
      multiply_commutative (b ^ n),
      multiply_associative,
    ]
  }

theorem Natural.power_multiply (n a b: Natural) : n ^ (a * b) = (n ^ a) ^ b := by
  induction a with
  | zero => rw [Natural.zero_def, zero_multiply, power_zero, one_power]
  | successor a ih => rw [successor.multiply, power_add, power_successor, ih, multiply.power]

def Natural.square (a: Natural) : Natural := a * a

theorem power_square (a: Natural) : a ^ (2: Natural) = a * a := rfl

-- theorem expand.quadratic (a b: Natural) : (a + b) ^ (2: Natural) = a ^ (2: Natural) + 2 * a * b + b ^ (2: Natural) := by
--   rw [
--     power_square,
--     power_square,
--     power_square,
--     multiply.distributive,
--     multiply.distributive.right,
--     multiply.commutative 2 a,
--     multiply.two,
--     multiply.distributive.right,
--     multiply.distributive.right,
--     ←add_associative,
--     ←add_associative,
--     multiply.commutative a b,
--   ]
