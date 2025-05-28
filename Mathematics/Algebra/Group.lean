class Inverse (T : Type) where
  inverseOfElement : T → T

postfix:max "⁻¹" => Inverse.inverseOfElement

class Group (T: Type) extends Mul T, Inverse T, OfNat T 1 where
associativity : ∀ a b c: T, a * (b * c) = (a * b) * c
identity : ∀ a: T, a * 1 = a ∧ 1 * a = a
inverse : ∀ a: T, a⁻¹ * a = 1 ∧ a * a⁻¹ = 1

class AbelianGroup (T: Type) extends Group T where
commutativity : ∀ a b : T, a * b = b * a

namespace groups

variable {T: Type} [Group T] (a b c: T)

theorem multiply.one (a: T) : a * 1 = a := (Group.identity a).left
theorem one.multiply (a: T) : 1 * a = a := (Group.identity a).right

-- theorem commutative [AbelianGroup T] (n m: T) : (n * m) = (n * m) := AbelianGroup.commutativity n m

theorem multiply.associative: ∀ a b c: T, a * (b * c) = (a * b) * c := Group.associativity

theorem inv.double : (a⁻¹)⁻¹ = a := by
  rw [←multiply.one (a⁻¹)⁻¹, ←(Group.inverse a).left, Group.associativity, (Group.inverse _).left, one.multiply]

theorem one.inverse : (1⁻¹) = (1: T) := by
  rw [←multiply.one 1⁻¹, (Group.inverse 1).1]

theorem multiply.eq_one_implies_eq (h : a * b = 1) : a⁻¹ = b := by
  rw [←multiply.one a⁻¹, ←h, Group.associativity, (Group.inverse a).left, one.multiply]

theorem inv.multiply : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply multiply.eq_one_implies_eq
  rw [←Group.associativity, Group.associativity b, (Group.inverse _).right, one.multiply, (Group.inverse a).right]

theorem multiply.left_cancel (h : a * b = a * c) : b = c := by
  rw [←one.multiply b, ←(Group.inverse a).left, ←Group.associativity, h, Group.associativity, (Group.inverse a).left, one.multiply c]

-- Note the symmetry with above
theorem multiply.right_cancel (h : b * a = c * a) : b = c := by
  rw [←multiply.one b, ←(Group.inverse a).right, Group.associativity, h, ←Group.associativity, (Group.inverse a).right, multiply.one c]

theorem multiply.injective_inverse : a⁻¹ = b⁻¹ ↔ a = b := by
  apply Iff.intro
  intro h1
  rw [←inv.double a, h1, inv.double]
  intro h2
  rw [h2]

theorem multiply.left_cancel_iff : a * b = a * c ↔ b = c := by
  apply Iff.intro
  exact @multiply.left_cancel T _ a b c
  intro h
  rw [h]

theorem multiply.right_cancel_iff : b * a = c * a ↔ b = c := by
  apply Iff.intro
  exact @multiply.right_cancel T _ a b c
  intro h
  rw [h]

theorem one.unique_right (e: T) : ∀ x: T, x * e = x → e = 1 := by
  intro x h1
  rw [←multiply.one x, ←multiply.associative, one.multiply] at h1
  exact (multiply.left_cancel_iff x e 1).1 h1

theorem one.unique_left (e: T) : ∀ x: T, e * x = x → e = 1 := by
  intro x h1
  rw [←one.multiply x, multiply.associative, multiply.one] at h1
  exact (multiply.right_cancel_iff x e 1).1 h1

end groups
