import Mathematics.Structures.Relation

class Inv (T : Type) where
  inv : T → T

postfix:max "⁻¹" => Inv.inverse

-- TODO to_additive
class Group (T: Type) extends Mul T, Inv T, OfNat T 1 :=
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
  rw [←multiply.one (a⁻¹)⁻¹, ←(Group.inverseerse a).left, Group.associativity, (Group.inverseerse _).left, one.multiply]

theorem one.inverseerse : (1⁻¹) = (1: T) := by
  rw [←multiply.one 1⁻¹, (Group.inverseerse 1).1]

theorem multiply.eq_one_implies_eq (h : a * b = 1) : a⁻¹ = b := by
  rw [←multiply.one a⁻¹, ←h, Group.associativity, (Group.inverseerse a).left, one.multiply]

theorem inv.multiply : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply multiply.eq_one_implies_eq
  rw [←Group.associativity, Group.associativity b, (Group.inverseerse _).right, one.multiply, (Group.inverseerse a).right]

theorem multiply.left_cancel (h : a * b = a * c) : b = c := by
  rw [←one.multiply b, ←(Group.inverseerse a).left, ←Group.associativity, h, Group.associativity, (Group.inverseerse a).left, one.multiply c]

-- Note the symmetry with above
theorem multiply.right_cancel (h : b * a = c * a) : b = c := by
  rw [←multiply.one b, ←(Group.inverseerse a).right, Group.associativity, h, ←Group.associativity, (Group.inverseerse a).right, multiply.one c]

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

class GroupHomomorphism (T U: Type) [Group T] [Group U] (f: T -> U) :=
map_mul : ∀ a b: T, f (a * b) = f a * f b

namespace group_homomorphism

def in_kernel {T U: Type} [Group T] [Group U] (f: T -> U) (a: T): Prop := f a = 1
def in_image {T U: Type} [Group T] [Group U] (f: T -> U) (b: U): Prop := ∃ a: T, f a = b

open groups

variable {T U: Type} [Group T] [Group U] (f: T -> U) [GroupHomomorphism T U f]

theorem map.multiply : ∀ a b: T, f (a * b) = f a * f b := GroupHomomorphism.map_mul

theorem map.one : f 1 = 1 := by
  apply groups.multiplytiply.left_cancel
  show f 1 * f 1 = f 1 * 1
  rw [←GroupHomomorphism.map_mul, multiply.one, multiply.one]

def id := fun (x: T) => x

theorem id.homomorphism : GroupHomomorphism T T id := {
  map_mul := by intros a b; exact rfl
}

theorem conjugation.homomorphism (c: T) : GroupHomomorphism T T (conjugation c) := {
  map_mul := by
    intros a b
    unfold conjugation
    rw [
      ←multiply.associative c b,
      multiply.associative _ c,
      ←multiply.associative _ _ c,
      (Group.inverseerse c).left,
      multiply.one,
      multiply.associative,
      multiply.associative
    ]
}

theorem homomorphism.compose { V: Type } [Group V] (f: T -> U) (g: U -> V) [GroupHomomorphism _ _ f] [GroupHomomorphism _ _ g]
  : GroupHomomorphism T V (g ∘ f) := {
    map_mul := by
      intros a b
      unfold Function.comp
      rw [←map.multiply, ←map.multiply]
}

theorem map.inverse (a : T) : f a⁻¹ = (f a)⁻¹ := by
  apply (multiply.left_cancel_iff (f a) (f a⁻¹) (f a)⁻¹).mp
  rw [←map.multiply, (Group.inverseerse a).right, (Group.inverseerse (f a)).right]
  exact @map.one T U _ _ f _

theorem map.multiplytiply.inverse (a b : T) : (f (a * b))⁻¹ = f b⁻¹ * f a⁻¹ := by
  rw [←map.multiply, ←inv.multiply, ←map.inverse]

-- TODO exponents
-- theorem map_pow (a : T) (n : Natural) : f a ^ n = (f a) ^ n := by
--   induction n with
--   | zero => rw [power.zero]
--   | successor n ih => rw [power.successor, ih]

end group_homomorphism

namespace random

variable {T: Type} [Group T]

def are_conjugate (x x': T) : Prop := ∃g, x' = conjugation g x

open groups in
instance : Relation T are_conjugate := {
  symmetric := by
    intro a b h1
    let ⟨g, h2⟩ := h1
    apply Exists.intro (Inv.inverse g)
    unfold conjugation at *
    rw [
      h2,
      inv.double,
      multiply.associative,
      ←multiply.associative _ g⁻¹ g,
      (Group.inverseerse g).1,
      multiply.one,
      multiply.associative,
      (Group.inverseerse g).1,
      one.multiply
    ]
  reflexivity := by
    intro a
    apply Exists.intro 1
    unfold conjugation at *
    rw [one.multiply, one.inverseerse, multiply.one]
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
instance (A B: Type) [Group A] [Group B] : Inv (Group.Product A B) := ⟨fun (g1, g2) => (g1⁻¹, g2⁻¹)⟩
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
    rw [mul_inv, mul_eq, (ga.inverseerse _).1, (gb.inverseerse _).1, mul_eq, (ga.inverseerse _).2, (gb.inverseerse _).2]
    exact ⟨one_left _ _, one_left _ _⟩
  identity := by
    intro a
    rw [mul_eq, one_left, (ga.identity _).1, (gb.identity _).1, mul_eq, (ga.identity _).2, (gb.identity _).2]
    exact ⟨rfl, rfl⟩
}

end product
