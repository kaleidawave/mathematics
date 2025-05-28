import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition

def Natural.multiply : Natural → Natural → Natural
| 0, _ => 0
| (successor a), b => (multiply a b) + b

instance : Mul Natural := ⟨Natural.multiply⟩

theorem zero.multiply (n: Natural) : 0 * n = 0 := rfl
theorem zerod.multiply (n: Natural) : Natural.zero * n = 0 := rfl
theorem successor.multiply (a b: Natural) : .successor a * b = a * b + b := rfl

theorem multiply.def (a b: Natural) : a * b = Natural.multiply a b := rfl

theorem multiply.zero (n: Natural) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => rw [successor.multiply, Natural.add.zero, ih]

theorem multiply.zerod (n: Natural): n * .zero = 0 := multiply.zero n

theorem multiply.one (n: Natural) : n * 1 = n := by
  induction n with
  | zero => rw [Natural.zero_def, zero.multiply]
  | successor n ih => rw [successor.multiply, ih, add.one]

theorem multiply.two (n: Natural) : n * 2 = n + n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    rw [successor.multiply, ih, add.successor, successor.add];
    exact add.two (n + n)

theorem multiply.successor (a b: Natural) : a * Natural.successor b = a * b + a := by
  induction a with
  | zero => rw [Natural.zero_def, zero.multiply, zero.multiply, zero.add]
  | successor a ih =>
    rw [successor.multiply, successor.multiply, ih, add.successor, add.successor];
    rw [add.associative _ b a, add.commutative b a, ←add.associative _ a b];

theorem one.multiply (n: Natural) : 1 * n = n := by
  induction n with
  | zero => rw [Natural.zero_def, multiply.zero]
  | successor n ih => rw [multiply.successor, ih, add.one]

theorem multiply.add (a b c: Natural) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => rw [Natural.zero_def, zero.multiply, zero.multiply, zero.multiply, zero.add]
  | successor a ih =>
    rw [successor.multiply, ih, successor.multiply, successor.multiply];
    ac_nf

def multiply.distributive := multiply.add

theorem multiply.commutative (a b: Natural) : a * b = b * a := by
  induction a with
  | zero => rw [Natural.zero_def, multiply.zero, zero.multiply]
  | successor a ih =>
    rw [multiply.successor, successor.multiply];
    exact (add.right_cancel (a * b) b (b * a)).mpr ih

theorem multiply.distributive.right (a b c: Natural) : (b + c) * a = a * b + a * c := by
  rw [multiply.commutative]
  exact multiply.add a b c

theorem multiply.associative (a b c: Natural) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [Natural.zero_def, multiply.zero, multiply.zero, multiply.zero]
  | successor c ih => rw [multiply.successor, multiply.successor, multiply.add, ih]

instance : Std.Commutative (α := Natural) (· * ·) := ⟨multiply.commutative⟩
instance : Std.Associative (α := Natural) (· * ·) := ⟨multiply.associative⟩

instance : Std.LawfulIdentity Natural.multiply 1 where
  left_id := one.multiply
  right_id := fun a => multiply.def a 1 ▸ multiply.one a

theorem multiply.eq.zero (a b: Natural) : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h1
  cases a with
  | zero => exact Or.inl Natural.zero_def
  | successor a => {
    rw [successor.multiply] at h1
    right;
    exact (add.eq.zero _ _ h1).right
  }

theorem multiply.neq.zero (a b: Natural) : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  {
    intro h1
    cases a with
    | zero => contradiction
    | successor a => {
      constructor
      {
        intro h2
        rw [h2] at h1
        contradiction
      }
      {
        intro h2
        rw [h2, multiply.zero] at h1
        contradiction
      }
    }
  }
  {
    intro h1 h2
    have h3 := multiply.eq.zero _ _ h2
    cases h3 with | inl h3 => exact h1.left h3 | inr h3 => exact h1.right h3
  }

theorem multiply.eq.one (a b: Natural) : a * b = 1 → a = 1 ∧ b = 1 := by
  intro h1
  induction a with
  | zero => contradiction
  | successor a ih => {
    have h2 := add.eq.one _ _ h1
    cases h2 with
    | inl h2 => {
      have b_eq := h2.right
      constructor
      rw [b_eq, multiply.one] at h1; exact h1;
      exact b_eq
    }
    | inr h2 => {
      have ⟨_, b_eq2⟩ := ih h2.left;
      rw [h2.right] at b_eq2
      contradiction
    }
  }
