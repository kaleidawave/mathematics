inductive Natural : Type
| zero
| successor (n: Natural)
deriving DecidableEq

def Natural.from.nat : Nat -> Natural
| Nat.zero => zero
| Nat.succ n => successor (Natural.from.nat n)

def Natural.to.nat : Natural -> Nat
| Natural.zero => .zero
| Natural.successor n => Nat.succ (Natural.to.nat n)

instance : Repr Natural where
  reprPrec := fun item => Repr.reprPrec (Natural.to.nat item)

def Natural.is_zero : Natural → Prop
| Natural.zero => True
| Natural.successor _n => False

def Natural.is_non_zero : Natural → Prop
| Natural.zero => False
| Natural.successor _n => True

instance (n : Nat) : OfNat Natural n where
  ofNat := Natural.from.nat n

def NonZeroNatural := { n: Natural // n ≠ 0 }

instance : Coe NonZeroNatural Natural where
  coe n := n.val

@[simp] theorem Natural.zero_def : Natural.zero = 0 := rfl

@[simp]
theorem successor.zero_eq_one : Natural.successor Natural.zero = 1 := rfl

theorem successor.inj (a b: Natural) : Natural.successor a = .successor b → a = b := Natural.successor.inj

@[simp]
theorem successor.neq.zero (n: Natural) : Natural.successor n ≠ 0 := Natural.noConfusion
