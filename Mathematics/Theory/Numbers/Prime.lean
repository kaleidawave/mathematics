import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Divides
import Mathematics.Structures.Numbers.Natural.Inequality

def is_prime (p: Natural) := p ≠ 1 ∧ ∀a: Natural, a ∣ p → a = 1 ∨ a = p
def is_composite (n: Natural) := n ≠ 1 ∧ ¬is_prime n
def is_unit (n: Natural) := n = 1

theorem primality_trichotomy (n: Natural): is_unit n ∨ is_composite n ∨ is_prime n := sorry

def Prime : Type := @Subtype Natural is_prime

/- Weak left cancelation -/
theorem mul_must_be_one (a b: Natural) (h1: a ≠ 0) : a = a * b → b = 1 := by
  cases b with
  | zero => rw [Natural.zero_def, Natural.multiply_zero]; intro h1; contradiction
  | successor b => {
    intro h2
    conv at h2 => rw [multiply.successor]; lhs; rw [←Natural.zero_add a];
    rw [Natural.add_right_cancel] at h2
    have d := multiply.eq.zero _ _ h2.symm
    cases d with
    | inl h => contradiction
    | inr h => rw [h]; rfl
  }

theorem even_not_prime (n: Natural) (h1: n ≠ 1) : ¬(is_prime (2 * n)) := by
  rintro ⟨_, h2⟩
  have h3 : 2 ∣ 2 * n := ⟨n, by rw [Natural.multiply_commutative]⟩
  have h4 := (h2 2) h3
  cases h4 with
  | inl h => contradiction
  | inr h => {
    have d := (mul_must_be_one 2 n) ( Ne.symm (ne_of_beq_false rfl)) h
    exact h1 d
  }

theorem greater_than_two (n: Natural) : 2 <= n → n ≠ 0 ∧ n ≠ 1 := by
  rintro ⟨w, h1⟩
  constructor
  intro h2;
  rw [h2] at h1;
  contradiction;

  intro h2;
  have b: (2: Natural) = 1 + 1 := rfl
  rw [h2, ←Natural.add_zero 1, b, Natural.add_associative, Natural.add_left_cancel _ 1 _, Natural.add_commutative, Natural.add_one] at h1;
  exact successor.neq.zero w h1

theorem multiple_not_prime (m n: Natural) (h1: n ≠ 1) (h2: 2 <= m) : ¬(is_prime (m * n)) := by
  rintro ⟨_, h3⟩
  have ⟨lhs, rhs⟩ := greater_than_two m h2
  have h4 : m ∣ m * n := ⟨n, by rw [Natural.multiply_commutative]⟩
  have h5 := (h3 m) h4
  cases h5 with
  | inl h => exact rhs h
  | inr h => {
    have d := (mul_must_be_one m n) lhs h
    exact h1 d
  }

theorem two_prime : is_prime 2 := by
  constructor
  trivial
  intro a h1
  -- have n: 2 ≠ 2 := by trivial
  have h2: a <= 2 := divides.less_than a 2 h1 (by trivial)
  match a with
  | 0 => {
    have d := zero_div.false 2 (by trivial) h1
    contradiction
  }
  | 1 => left; rfl
  | 2 => right; rfl

theorem three_prime : is_prime 3 := by
  constructor
  trivial
  intro a h1
  -- have n: 2 ≠ 2 := by trivial
  have h2: a <= 3 := divides.less_than a 3 h1 (by trivial)
  match a with
  | 0 => {
    have d := zero_div.false 3 (by trivial) h1
    contradiction
  }
  | 1 => left; rfl
  | 2 => {
    obtain ⟨c, h1⟩ := h1
    exact False.elim (
      by cases c with
      | zero => contradiction
      | successor c => {
        rw [successor.multiply, add.two] at h1
        replace h2: c * 2 = 1 := successor.inj (successor.inj h1)
        rw [multiply.two] at h2
        cases Natural.add_eq_one c c h2 with
        | inl h2 => nomatch h2.left, h2.right
        | inr h2 => nomatch h2.left, h2.right
      }
    )
  }
  | 3 => right; rfl

theorem four_not_prime : ¬is_prime 4 := by
  intro ⟨_, h1⟩
  specialize h1 2 ⟨2, rfl⟩
  cases h1 <;> trivial

-- TODO separate q
def SophieGermainPrime (p q: Prime): Prop := p.val = 2 * q.val + 1

-- def FermatWitness (n: Natural) (base: Natural): Prop := base ^ n ≡ base [mod n]

-- def CarmichaelNumber (p': Natural): Prop := ¬is_prime p' ∧ ∀a: Natural, FermatWitness p' a

-- example : CarmichaelNumber 561 := sorry

-- theorem FermatCompositeWitness (n: Natural) (base: Natural): Prop := base ^ n ≡ base [mod n]
