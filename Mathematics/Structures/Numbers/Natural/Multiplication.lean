import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition

def Natural.multiply : Natural → Natural → Natural
| 0, _ => 0
| (successor a), b => (multiply a b) + b

instance : Mul Natural := ⟨Natural.multiply⟩

theorem zero.multiply (n: Natural) : 0 * n = 0 := rfl
theorem successor.multiply (a b: Natural) : .successor a * b = a * b + b := rfl

theorem multiply.zero (n: Natural) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => rw [successor.multiply, Natural.add.zero, ih]

theorem multiply.one (n: Natural) : n * 1 = n := by
  induction n with
  | zero => rw [Natural.zero_def, zero.multiply]
  | successor n ih => rw [successor.multiply, ih, add.one]

theorem multiply.two (n: Natural) : n * 2 = n + n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    rw [
      successor.multiply,
      ih,
      add.successor,
      Natural.add.commutative (.successor n) n,
      ←add.successor,
      ←add.one,
      ←add.one,
      Natural.add.associative,
      Natural.add.associative,
      ←Natural.add.associative _ 1 1
    ]; rfl

theorem multiply.successor (a b: Natural) : a * Natural.successor b = a * b + a := by
  induction a with
  | zero => rw [Natural.zero_def, zero.multiply, zero.multiply, Natural.zero.add]
  | successor a ih => rw [
    successor.multiply,
    successor.multiply,
    ih,
    ←Natural.add.associative,
    add.successor,
    ←Natural.add.associative,
    add.successor b,
    Natural.add.commutative a
  ]

theorem one.multiply (n: Natural) : 1 * n = n := by
  induction n with
  | zero => rw [Natural.zero_def, multiply.zero]
  | successor n ih => rw [multiply.successor, ih, add.one]

-- Distributivity #TODO got to be a shorter way
theorem multiply.add (a b c: Natural) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => rw [Natural.zero_def, zero.multiply, zero.multiply, zero.multiply, Natural.zero.add]
  | successor a ih => rw [
    successor.multiply,
    ih,
    successor.multiply,
    successor.multiply,
    ←Natural.add.associative _ b _,
    Natural.add.commutative b (a * c + c),
    ←Natural.add.associative (a * c),
    Natural.add.commutative c b,
    Natural.add.associative,
    Natural.add.associative,
    Natural.add.associative,
  ]

def multiply.distributive := multiply.add

theorem multiply.commutative (a b: Natural) : a * b = b * a := by
  induction a with
  | zero => rw [Natural.zero_def, multiply.zero, zero.multiply]
  | successor a ih => rw [multiply.successor, successor.multiply]; exact (add.left_cancel _ _ _).2 ih

theorem multiply.distributive.right (a b c: Natural) : (b + c) * a = a * b + a * c := by
  rw [multiply.commutative]
  exact multiply.add a b c

theorem multiply.associative (a b c: Natural) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [Natural.zero_def, multiply.zero, multiply.zero, multiply.zero]
  | successor c ih => rw [multiply.successor, multiply.successor, multiply.add, ih]

theorem multiply.eq.zero (a b: Natural) : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h1
  induction a with
  | zero => exact Or.inl Natural.zero_def
  -- TODO doesn't use ih!!
  | successor a _ih => {
    rw [successor.multiply] at h1
    have h2 := sum_eq_zero_implies_either_zero _ _ h1
    exact Or.inr h2.right
  }
