inductive Natural : Type
| zero
| successor (n: Natural)
deriving DecidableEq

@[reducible]
def Natural.from.nat : Nat -> Natural
| Nat.zero => zero
| Nat.succ n => successor (Natural.from.nat n)

@[reducible]
def Natural.to.nat : Natural -> Nat
| Natural.zero => .zero
| Natural.successor n => Nat.succ (Natural.to.nat n)

instance (n: Nat) : OfNat Natural n where
  ofNat := Natural.from.nat n

instance : Zero Natural := ⟨Natural.zero⟩

instance : Repr Natural where
  reprPrec := fun item => Repr.reprPrec (Natural.to.nat item)

def Natural.is_zero : Natural → Prop
| Natural.zero => True
| Natural.successor _n => False

def Natural.is_non_zero : Natural → Prop
| Natural.zero => False
| Natural.successor _n => True

def NonZeroNatural := Subtype fun n: Natural => n ≠ 0

instance : Coe NonZeroNatural Natural where
  coe n := n.val

@[simp]
theorem Natural.zero_def : Natural.zero = 0 := rfl

@[simp]
theorem successor.zero_eq_one : Natural.successor 0 = 1 := rfl

@[simp]
theorem successor.zerod_eq_one : Natural.successor Natural.zero = 1 := rfl

theorem successor.inj {a b: Natural} : Natural.successor a = .successor b → a = b := Natural.successor.inj

theorem successor.pure {a b: Natural} : a = b → Natural.successor a = .successor b := fun x => congrArg Natural.successor x

theorem successor.iff {a b: Natural} : a = b ↔ Natural.successor a = .successor b := ⟨successor.pure, successor.inj⟩

@[simp]
theorem successor.neq.zero (n: Natural) : Natural.successor n ≠ 0 := Natural.noConfusion

@[simp]
theorem one.neq.zero: (1: Natural) ≠ 0 := Natural.noConfusion

@[simp]
theorem successor.neq.successor (n: Natural) : Natural.successor n ≠ n := by
  induction n with
  | zero => exact ne_of_beq_false rfl
  | successor n ih => {
    intro h1
    have d := successor.inj h1
    exact ih d
  }

def Natural.predecessor : Natural → Natural
| zero => zero
| successor n => n

theorem Natural.successor.predecessor (n: Natural) : n.successor.predecessor = n := rfl
theorem Natural.predecessor.successor (n: Natural) (h1: n ≠ 0) : n.predecessor.successor = n := by
  induction n with
  | zero => contradiction
  | successor n ih => exact Natural.successor.predecessor _
