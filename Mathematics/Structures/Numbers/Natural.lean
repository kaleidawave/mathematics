inductive Natural : Type
| zero
| successor (n: Natural)
deriving Repr

def Natural.from.nat : Nat -> Natural
| Nat.zero => zero
| Nat.succ n => successor (Natural.from.nat n)

instance (n : Nat) : OfNat Natural n where
  ofNat := Natural.from.nat n

@[simp]
theorem zero.eq_zero : Natural.zero = 0 := rfl

@[simp]
theorem successor.zero_eq_one : Natural.successor Natural.zero = 1 := rfl

theorem successor.inj (a b: Natural) : Natural.successor a = .successor b → a = b := Natural.successor.inj

namespace addition
open Natural

def Natural.add : Natural → Natural → Natural
| zero, a => a
| successor a, b => successor (add a b)

instance : Add Natural := ⟨Natural.add⟩

theorem zero.add (a: Natural) : 0 + a = a := rfl

theorem successor.add (a b: Natural) : successor a + b = successor (a + b) := rfl

theorem add.zero (a: Natural) : a + 0 = a := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem add.one (a: Natural) : a + 1 = successor a := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem add.successor (a b: Natural) : a + successor b = successor (a + b) := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, successor.add, n_ih]

theorem add.inverse.cancel (a b c: Natural) : a = b → a + c = b + c := by
  intro h1
  induction c with
  | zero => rw [h1]
  | successor n n_ih => rw [add.successor, add.successor, n_ih]

theorem add.commutative (a b: Natural) : a + b = b + a := by
  induction a with
  | zero => rw [zero.eq_zero, add.zero, zero.add]
  | successor n n_ih => rw [successor.add, add.successor, n_ih]

theorem add.associative (a b c: Natural) : a + (b + c) = a + b + c := by
  induction c with
  | zero => rw [zero.eq_zero, add.zero, add.zero]
  | successor n n_ih => rw [add.successor, add.successor, add.successor, n_ih]

theorem add.left_cancel (a b c: Natural) : a + b = c + b ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [zero.eq_zero, add.zero, add.zero] at h1; exact h1
  | successor n ih => {
    rw [add.successor, add.successor] at h1
    exact ih (successor.inj _ _ h1)
  }
  intro h2
  rw [h2, add.commutative]

theorem add.right_cancel (a b c: Natural) : b + a = b + c ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [←zero.add a, ←zero.eq_zero, h1, zero.eq_zero, zero.add]
  | successor n ih => {
    rw [successor.add, successor.add] at h1
    exact ih (successor.inj _ _ h1)
  }
  intro h2
  rw [h2]

-- TODO should use add.left_cancel
theorem add.left_zero_cancel (a b: Natural) : a + b = a → b = 0 := by
  intro h1
  induction a with
  | zero => rw [zero.eq_zero, zero.add] at h1; exact h1
  | successor n ih => {
    rw [successor.add] at h1
    exact ih (successor.inj _ _ h1)
  }

theorem successor.neq.zero (n: Natural) : successor n ≠ 0 := Natural.noConfusion

-- TODO should use add.left_cancel
theorem sum_eq_zero_implies_either_zero (a b: Natural) : a + b = 0 → a = 0 ∧ b = 0 := by
  intro h1
  induction a with
  | zero => exact ⟨zero.eq_zero, by { rw [zero.eq_zero] at h1; exact add.left_zero_cancel _ _ h1 }⟩
  | successor n _ => {
    rw [successor.add] at h1
    contradiction
  }

end addition

namespace less_than

def Natural.less_than.equal (a b : Natural) : Prop := ∃c: Natural, a + c = b

def Natural.less_than.equal' : Natural → Natural → Bool
| .successor n, .successor m => Natural.less_than.equal' n m
| .successor _, .zero => false
| .zero, .successor _ => true
| .zero, .zero => true

instance : LE Natural := ⟨Natural.less_than.equal⟩

theorem Natural.less_than.equal.def (a b : Natural) : (a <= b) = Natural.less_than.equal a b := rfl

theorem Natural.less_than.equal.iff (a b : Natural) :
    Natural.less_than.equal a b ↔ Natural.less_than.equal' a b := by
  induction a generalizing b
  · cases b
    · simp [less_than.equal, less_than.equal']
      exists .zero
    next b' =>
      simp [less_than.equal, less_than.equal']
      exists .successor b'
  next a' ih =>
    cases b
    · simp [less_than.equal, less_than.equal', addition.successor.add]
      intro ⟨w, h⟩
      have h2 := addition.successor.neq.zero (a' + w)
      exact h2 h
    next b' =>
      simp [less_than.equal, less_than.equal', ← ih, addition.successor.add]

instance (a b : Natural) : Decidable (a <= b) := by
  rw [Natural.less_than.equal.def, Natural.less_than.equal.iff a b]
  infer_instance

-- TODO extract
class PartialOrder (T: Type) (relation: T → T → Prop) :=
reflexivity : ∀ a: T, relation a a
antisymmetric : ∀ a b: T, (relation a b) ∧ (relation b a) → a = b
transitivity : ∀ a b c: T, (relation a b) ∧ (relation b c) → (relation a c)

open addition in
instance : PartialOrder Natural LE.le := {
  reflexivity := by
    intro a
    unfold LE.le
    exists 0
    exact add.zero a
  antisymmetric := by
    intro a b
    unfold LE.le
    intro h1
    let ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ := h1
    rw [←h1, ←add.associative] at h2
    have h3 : c1 + c2 = 0 := add.left_zero_cancel a (c1 + c2) h2
    have h4 : c1 = 0 := (sum_eq_zero_implies_either_zero c1 c2 h3).left
    rw [h4, add.zero] at h1
    exact h1
  transitivity := by
    intro a b c
    unfold LE.le
    intro h1
    let ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ := h1
    apply Exists.intro (c1 + c2)
    rw [←h1, ←add.associative] at h2
    exact h2
}

theorem not.le.not.equal (a b: Natural) (h1: ¬(a <= b)): a ≠ b := by
  intro h2
  rw [h2] at h1
  have h3: b <= b := PartialOrder.reflexivity b
  exact h1 h3

end less_than

namespace min_max

open less_than

def Natural.min.of (n m: Natural) : Natural := if n <= m then n else m

-- Similar to Exists
-- TODO https://leanprover-commutativeunity.github.io/mathlib4.docs/Mathlib/Init/Data/Nat/Lemmas.html#Nat.find
def Natural.min.under (n: Natural) (p: Natural → Prop) : Prop := p n ∧ ¬∃m: Natural, m <= n → p m

def Natural.max.of (n m: Natural) : Natural := if n <= m then m else n

example : min 2 4 = 2 := by unfold min; rfl

end min_max

namespace multiplication

open Natural addition

def Natural.multiply : Natural → Natural → Natural
| 0, _ => 0
| (successor a), b => (multiply a b) + b

instance : Mul Natural := ⟨Natural.multiply⟩

theorem zero.multiply (n: Natural) : 0 * n = 0 := rfl
theorem successor.multiply (a b: Natural) : successor a * b = a * b + b := rfl

theorem multiply.zero (n: Natural) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => rw [successor.multiply, add.zero, ih]

theorem multiply.one (n: Natural) : n * 1 = n := by
  induction n with
  | zero => rw [zero.eq_zero, zero.multiply]
  | successor n ih => rw [successor.multiply, ih, add.one]

theorem multiply.two (n: Natural) : n * 2 = n + n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    rw [
      successor.multiply,
      ih,
      add.successor,
      add.commutative (.successor n) n,
      ←add.successor,
      ←add.one,
      ←add.one,
      add.associative,
      add.associative,
      ←add.associative _ 1 1
    ]; rfl

theorem multiply.successor (a b: Natural) : a * successor b = a * b + a := by
  induction a with
  | zero => rw [zero.eq_zero, zero.multiply, zero.multiply, zero.add]
  | successor a ih => rw [successor.multiply, successor.multiply, ih, ←add.associative, add.successor, ←add.associative, add.successor b, add.commutative a]

theorem one.multiplytiply (n: Natural) : 1 * n = n := by
  induction n with
  | zero => rw [zero.eq_zero, multiply.zero]
  | successor n ih => rw [multiply.successor, ih, add.one]

-- Distributivity #TODO got to be a shorter way
theorem multiply.add (a b c: Natural) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => rw [zero.eq_zero, zero.multiply, zero.multiply, zero.multiply, zero.add]
  | successor a ih => rw [
    successor.multiply,
    ih,
    successor.multiply,
    successor.multiply,
    ←add.associative _ b _,
    add.commutative b (a * c + c),
    ←add.associative (a * c),
    add.commutative c b,
    add.associative,
    add.associative,
    add.associative,
  ]

def multiply.distributive := multiply.add

theorem multiply.commutative (a b: Natural) : a * b = b * a := by
  induction a with
  | zero => rw [zero.eq_zero, multiply.zero, zero.multiply]
  | successor a ih => rw [multiply.successor, successor.multiply]; exact (add.left_cancel _ _ _).2 ih

theorem multiply.associative (a b c: Natural) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [zero.eq_zero, multiply.zero, multiply.zero, multiply.zero]
  | successor c ih => rw [multiply.successor, multiply.successor, multiply.add, ih]

theorem multiply.eq.zero (a b: Natural) : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h1
  induction a with
  | zero => exact Or.inl zero.eq_zero
  -- TODO doesn't use ih!!
  | successor a _ih => {
    rw [successor.multiply] at h1
    have h2 := sum_eq_zero_implies_either_zero _ _ h1
    exact Or.inr h2.right
  }

end multiplication

namespace factorial

open Natural

/-- TODO class and syntax? -/
def Natural.factorial : Natural → Natural
| 0 => 1
-- TODO can bind and reuse?
| (successor a) => (successor a) * (factorial a)

-- #eval (3: Natural).factorial # Doesn't work :?

-- TODO chose function etc

end factorial

namespace exponentiation

open Natural multiplication

def Natural.power : Natural → Natural → Natural
| _, 0 => 1
| a, (successor b) => (power a b) * a

instance : Pow Natural Natural := ⟨Natural.power⟩

theorem power.zero (n: Natural) : n ^ (0: Natural) = 1 := rfl
theorem power.successor (m n: Natural) : n ^ successor m = n ^ m * n := rfl

theorem power.one (n: Natural) : n ^ (1: Natural) = n := by
  rw [←successor.zero_eq_one, power.successor, zero.eq_zero, power.zero, one.multiplytiply]

theorem one.power (n: Natural) : (1: Natural) ^ n = 1 := by
  induction n with
  | zero => exact zero.eq_zero ▸ power.zero 1
  | successor n ih => rw [power.successor, multiply.one, ih]

theorem power.add (n a b: Natural) : n ^ (a + b) = n ^ a * n ^ b := by
  induction a with
  | zero => rw [zero.eq_zero, addition.zero.add, power.zero, one.multiplytiply]
  | successor a ih => rw [addition.successor.add, power.successor, power.successor, ih, multiply.associative, multiply.commutative _ n, multiply.associative]

-- TODO simpler ?
theorem multiply.power (n a b: Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [zero.eq_zero, power.zero, power.zero, power.zero, multiply.one]
  | successor n ih => rw [
    power.successor,
    power.successor,
    power.successor,
    ih,
    multiply.associative,
    multiply.associative,
    multiply.commutative (b ^ n),
    multiply.commutative (b ^ n),
    multiply.associative,
  ]

theorem power.multiply (n a b: Natural) : n ^ (a * b) = (n ^ a) ^ b := by
  induction a with
  | zero => rw [zero.eq_zero, zero.multiply, power.zero, one.power]
  | successor a ih => rw [successor.multiply, power.add, power.successor, ih, multiply.power]

end exponentiation

namespace divides

open multiplication

def divides (f: Natural) (n: Natural) : Prop := ∃m: Natural, m * n = f

infix:20 " ∣ " => divides

example : 8 ∣ 4 := ⟨2, rfl⟩

theorem divides.self (n: Natural) : n ∣ n := ⟨1, one.multiplytiply n⟩

theorem one.divides (n: Natural) : n ∣ 1 := ⟨n, multiply.one n⟩

end divides

namespace modulo_congurence

def Natural.congruence (a b m : Natural) : Prop := ∃n: Natural, b = m * n + a

notation a " ≡ " b " mod " m  => Natural.congruence a b m

example : 5 ≡ 7 mod 2 := ⟨1, rfl⟩

theorem congruence.add (a b m : Natural) : (a ≡ b mod m) → (a ≡ (b + m) mod m) := by
  intro h1
  let ⟨n, h2⟩ := h1
  apply Exists.intro (n + 1)
  rw [
    h2,
    multiplication.multiply.add,
    multiplication.multiply.one,
    ←addition.add.associative,
    addition.add.commutative a m,
    addition.add.associative
  ]

-- TODO congruence class

end modulo_congurence
