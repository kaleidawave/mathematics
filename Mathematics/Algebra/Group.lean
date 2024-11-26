import Mathematics.Structures.Relation

class Inverse (T : Type) where
  inverse' : T → T

postfix:max "⁻¹" => Inverse.inverse'

class Group (T: Type) extends Mul T, Inverse T, OfNat T 1 :=
associativity : ∀ a b c: T, a * (b * c) = (a * b) * c
identity : ∀ a: T, a * 1 = a ∧ 1 * a = a
inverse : ∀ a: T, a⁻¹ * a = 1 ∧ a * a⁻¹ = 1

class AbelianGroup (T: Type) extends Group T :=
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

def conjugation { T: Type } [Group T] (c: T) := fun (x: T) => c * x * c⁻¹

namespace random

variable {T: Type} [Group T]

def are_conjugate (x x': T) : Prop := ∃g, x' = conjugation g x

open groups in
instance : Relation T are_conjugate := {
  symmetric := by
    intro a b h1
    let ⟨g, h2⟩ := h1
    apply Exists.intro g⁻¹
    unfold conjugation at *
    rw [
      h2,
      inv.double,
      multiply.associative,
      ←multiply.associative _ g⁻¹ g,
      (Group.inverse g).1,
      multiply.one,
      multiply.associative,
      (Group.inverse g).1,
      one.multiply
    ]
  reflexivity := by
    intro a
    apply Exists.intro 1
    unfold conjugation at *
    rw [one.multiply, one.inverse, multiply.one]
  transitivity := by
    intro a b c h1
    let ⟨⟨g1, h2⟩, ⟨g2, h3⟩⟩ := h1
    apply Exists.intro (g2 * g1)
    unfold conjugation at *
    rw [h3, h2, inv.multiply, multiply.associative, multiply.associative, multiply.associative]
}

end random

namespace product

def Group.Product (A B: Type) [Group A] [Group B] : Type := A × B

instance (A B: Type) [Group A] [Group B] : Mul (Group.Product A B) := ⟨fun (g1, g2) (h1, h2) => (g1 * h1, g2 * h2)⟩
instance (A B: Type) [Group A] [Group B] : Inverse (Group.Product A B) := ⟨fun (g1, g2) => (g1⁻¹, g2⁻¹)⟩
instance (A B: Type) [Group A] [Group B] : OfNat (Group.Product A B) 1 := ⟨(1, 1)⟩

theorem mul_eq (A B: Type) [Group A] [Group B] (a b: Group.Product A B) : a * b = (a.1 * b.1, a.2 * b.2) := rfl
theorem mul_inv (A B: Type) [Group A] [Group B] (a: Group.Product A B) : a⁻¹ = (a.1⁻¹, a.2⁻¹) := rfl
theorem one_left (A B: Type) [Group A] [Group B] : (1: Group.Product A B) = (1, 1) := rfl

instance (A B: Type) {ga: Group A} {gb: Group B} : Group (Group.Product A B) := {
  associativity := by
    intro a b c
    rw [mul_eq, mul_eq, ga.associativity, gb.associativity]
    rfl
  inverse := by
    intro a
    rw [mul_inv, mul_eq, (ga.inverse _).1, (gb.inverse _).1, mul_eq, (ga.inverse _).2, (gb.inverse _).2]
    exact ⟨one_left _ _, one_left _ _⟩
  identity := by
    intro a
    rw [mul_eq, one_left, (ga.identity _).1, (gb.identity _).1, mul_eq, (ga.identity _).2, (gb.identity _).2]
    exact ⟨rfl, rfl⟩
}

end product
