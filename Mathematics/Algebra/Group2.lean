import Mathematics.Macros.GroupTransport

class Inv (T : Type) where
  inv : T → T

postfix:max "⁻¹" => Inv.inv

class Mul.Group (T: Type) extends Mul T, Inv T, OfNat T 1 :=
associativity : ∀ a b c: T, a * (b * c) = (a * b) * c
identity : ∀ a: T, a * 1 = a ∧ 1 * a = a
inverse : ∀ a: T, a⁻¹ * a = 1 ∧ a * a⁻¹ = 1

class Add.Group (T: Type) extends Add T, Neg T, OfNat T 0 :=
associativity : ∀ a b c: T, a + (b + c) = (a + b) + c
identity : ∀ a: T, a + 0 = a ∧ 0 + a = a
inverse : ∀ a: T, -a + a = 0 ∧ a + -a = 0

-- @[to_additive]
class Mul.AbelianGroup (T: Type) extends Mul.Group T :=
commutativity : ∀ a b : T, a * b = b * a

class Add.AbelianGroup (T: Type) extends Add.Group T :=
commutativity : ∀ a b : T, a + b = b + a

@[to_additive]
theorem Mul.X (T: Type) [Mul.Group T] (a: T) : a * 1 = a := (Mul.Group.identity a).left

#print Mul.X
#print Add.X

@[to_additive]
theorem Mul.Dist2 (T: Type) [Mul.AbelianGroup T] (a b c: T) : a * (b * c) = (b * a) * c := by
  conv => rhs; lhs; rw [Mul.AbelianGroup.commutativity];
  exact Mul.Group.associativity _ _ _

#check Add.Dist2
