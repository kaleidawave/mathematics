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

theorem add.inv.cancel (a b c: Natural) : a = b → a + c = b + c := by
  intro h1
  induction c with
  | zero => rw [h1]
  | successor n n_ih => rw [add.successor, add.successor, n_ih]

theorem add.comm (a b: Natural) : a + b = b + a := by
  induction a with
  | zero => rw [zero.eq_zero, add.zero, zero.add]
  | successor n n_ih => rw [successor.add, add.successor, n_ih]

theorem add.assoc (a b c: Natural) : a + (b + c) = a + b + c := by
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
  rw [h2, add.comm]

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
    rw [←h1, ←add.assoc] at h2
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
    rw [←h1, ←add.assoc] at h2
    exact h2
}

theorem not.le.not.equal (a b: Natural) (h1: ¬(a <= b)): a ≠ b := by
  intro h2
  rw [h2] at h1
  have h3: b <= b := PartialOrder.reflexivity b
  exact h1 h3

end less_than

namespace min.max

open less_than

def Natural.min.of (n m: Natural) : Natural := if n <= m then n else m

-- Similar to Exists
-- TODO https://leanprover-community.github.io/mathlib4.docs/Mathlib/Init/Data/Nat/Lemmas.html#Nat.find
def Natural.min.under (n: Natural) (p: Natural → Prop) : Prop := p n ∧ ¬∃m: Natural, m <= n → p m

def Natural.max.of (n m: Natural) : Natural := if n <= m then m else n

example : min 2 4 = 2 := by unfold min; rfl

end min.max

namespace multiplication

open Natural addition

def Natural.mul : Natural → Natural → Natural
| 0, _ => 0
| (successor a), b => (mul a b) + b

instance : Mul Natural := ⟨Natural.mul⟩

theorem zero.mul (n: Natural) : 0 * n = 0 := rfl
theorem successor.mul (a b: Natural) : successor a * b = a * b + b := rfl

theorem mul.zero (n: Natural) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => rw [successor.mul, add.zero, ih]

theorem mul.one (n: Natural) : n * 1 = n := by
  induction n with
  | zero => rw [zero.eq_zero, zero.mul]
  | successor n ih => rw [successor.mul, ih, add.one]

theorem mul.successor (a b: Natural) : a * successor b = a * b + a := by
  induction a with
  | zero => rw [zero.eq_zero, zero.mul, zero.mul, zero.add]
  | successor a ih => rw [successor.mul, successor.mul, ih, ←add.assoc, add.successor, ←add.assoc, add.successor b, add.comm a]

theorem one.mul (n: Natural) : 1 * n = n := by
  induction n with
  | zero => rw [zero.eq_zero, mul.zero]
  | successor n ih => rw [mul.successor, ih, add.one]

-- Distributivity #TODO got to be a shorter way
theorem mul.add (a b c: Natural) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => rw [zero.eq_zero, zero.mul, zero.mul, zero.mul, zero.add]
  | successor a ih => rw [
    successor.mul,
    ih,
    successor.mul,
    successor.mul,
    ←add.assoc _ b _,
    add.comm b (a * c + c),
    ←add.assoc (a * c),
    add.comm c b,
    add.assoc,
    add.assoc,
    add.assoc,
  ]

theorem mul.comm (a b: Natural) : a * b = b * a := by
  induction a with
  | zero => rw [zero.eq_zero, mul.zero, zero.mul]
  | successor a ih => rw [mul.successor, successor.mul]; exact (add.left_cancel _ _ _).2 ih

theorem mul.assoc (a b c: Natural) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [zero.eq_zero, mul.zero, mul.zero, mul.zero]
  | successor c ih => rw [mul.successor, mul.successor, mul.add, ih]

theorem mul.eq.zero (a b: Natural) : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h1
  induction a with
  | zero => exact Or.inl zero.eq_zero
  -- TODO doesn't use ih!!
  | successor a _ih => {
    rw [successor.mul] at h1
    have h2 := sum_eq_zero_implies_either_zero _ _ h1
    exact Or.inr h2.right
  }

end multiplication

namespace exponentiation

open Natural multiplication

def Natural.pow : Natural → Natural → Natural
| _, 0 => 1
| a, (successor b) => (pow a b) * a

instance : Pow Natural Natural := ⟨Natural.pow⟩

theorem pow.zero (n: Natural) : n ^ 0 = 1 := rfl
theorem pow.successor (m n: Natural) : n ^ successor m = n ^ m * n := rfl

theorem pow.one (n: Natural) : n ^ 1 = n := by
  rw [←successor.zero_eq_one, pow.successor, zero.eq_zero, pow.zero, one.mul]

theorem one.pow (n: Natural) : 1 ^ n = 1 := by
  induction n with
  | zero => exact zero.eq_zero ▸ pow.zero 1
  | successor n ih => rw [pow.successor, mul.one, ih]

theorem pow.add (n a b: Natural) : n ^ (a + b) = n ^ a * n ^ b := by
  induction a with
  | zero => rw [zero.eq_zero, addition.zero.add, pow.zero, one.mul]
  | successor a ih => rw [addition.successor.add, pow.successor, pow.successor, ih, mul.assoc, mul.comm _ n, mul.assoc]

-- TODO simpler ?
theorem mul.pow (n a b: Natural) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [zero.eq_zero, pow.zero, pow.zero, pow.zero, mul.one]
  | successor n ih => rw [
    pow.successor,
    pow.successor,
    pow.successor,
    ih,
    mul.assoc,
    mul.assoc,
    mul.comm (b ^ n),
    mul.comm (b ^ n),
    mul.assoc,
  ]

theorem pow.mul (n a b: Natural) : n ^ (a * b) = (n ^ a) ^ b := by
  induction a with
  | zero => rw [zero.eq_zero, zero.mul, pow.zero, one.pow]
  | successor a ih => rw [successor.mul, pow.add, pow.successor, ih, mul.pow]

end exponentiation

namespace divides

open multiplication

def divides (f: Natural) (n: Natural) : Prop := ∃m: Natural, m * n = f

example : divides 8 4 := ⟨2, rfl⟩

theorem divides.self (n: Natural) : divides n n := ⟨1, one.mul n⟩

theorem one.divides (n: Natural) : divides n 1 := ⟨n, mul.one n⟩

end divides

namespace modulo_congurence

def Natural.cong (a b m : Natural) : Prop := ∃n: Natural, b = m * n + a

notation a " ≡ " b " mod " m  => Natural.cong a b m

example : 5 ≡ 7 mod 2 := by apply Exists.intro 1; rfl

theorem congruence.add (a b m : Natural) : (a ≡ b mod m) → (a ≡ (b + m) mod m) := by
  intro h1
  let ⟨n, h2⟩ := h1
  apply Exists.intro (n + 1)
  rw [
    h2,
    multiplication.mul.add,
    multiplication.mul.one,
    ←addition.add.assoc,
    addition.add.comm a m,
    addition.add.assoc
  ]

-- TODO congruence class

end modulo_congurence
