import Mathematics.Structures.Relation

class Inv (T : Type) where
  inv : T → T

postfix:max "⁻¹" => Inv.inv

-- TODO to_additive
class Group (T: Type) extends Mul T, Inv T, OfNat T 1 :=
associativity : ∀ a b c: T, a * (b * c) = (a * b) * c
identity : ∀ a: T, a * 1 = a ∧ 1 * a = a
inverse : ∀ a: T, a⁻¹ * a = 1 ∧ a * a⁻¹ = 1

class AbelianGroup (T: Type) extends Group T :=
commutativity : ∀ a b : T, a * b = b * a

namespace groups

variable {T: Type} [Group T] (a b c: T)

theorem mul.one (a: T) : a * 1 = a := (Group.identity a).left
theorem one.mul (a: T) : 1 * a = a := (Group.identity a).right

-- theorem comm [AbelianGroup T] (n m: T) : (n * m) = (n * m) := AbelianGroup.commutativity n m

theorem mul.assoc: ∀ a b c: T, a * (b * c) = (a * b) * c := Group.associativity

theorem inv.double : (a⁻¹)⁻¹ = a := by
  rw [←mul.one (a⁻¹)⁻¹, ←(Group.inverse a).left, Group.associativity, (Group.inverse _).left, one.mul]

theorem one.inverse : (1⁻¹) = (1: T) := by
  rw [←mul.one 1⁻¹, (Group.inverse 1).1]

theorem mul.eq_one_implies_eq (h : a * b = 1) : a⁻¹ = b := by
  rw [←mul.one a⁻¹, ←h, Group.associativity, (Group.inverse a).left, one.mul]

theorem inv.mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply mul.eq_one_implies_eq
  rw [←Group.associativity, Group.associativity b, (Group.inverse _).right, one.mul, (Group.inverse a).right]

theorem mul.left_cancel (h : a * b = a * c) : b = c := by
  rw [←one.mul b, ←(Group.inverse a).left, ←Group.associativity, h, Group.associativity, (Group.inverse a).left, one.mul c]

-- Note the symmetry with above
theorem mul.right_cancel (h : b * a = c * a) : b = c := by
  rw [←mul.one b, ←(Group.inverse a).right, Group.associativity, h, ←Group.associativity, (Group.inverse a).right, mul.one c]

theorem mul.injective_inverse : a⁻¹ = b⁻¹ ↔ a = b := by
  apply Iff.intro
  intro h1
  rw [←inv.double a, h1, inv.double]
  intro h2
  rw [h2]

theorem mul.left_cancel_iff : a * b = a * c ↔ b = c := by
  apply Iff.intro
  exact @mul.left_cancel T _ a b c
  intro h
  rw [h]

theorem mul.right_cancel_iff : b * a = c * a ↔ b = c := by
  apply Iff.intro
  exact @mul.right_cancel T _ a b c
  intro h
  rw [h]

theorem one.unique_right (e: T) : ∀ x: T, x * e = x → e = 1 := by
  intro x h1
  rw [←mul.one x, ←mul.assoc, one.mul] at h1
  exact (mul.left_cancel_iff x e 1).1 h1

theorem one.unique_left (e: T) : ∀ x: T, e * x = x → e = 1 := by
  intro x h1
  rw [←one.mul x, mul.assoc, mul.one] at h1
  exact (mul.right_cancel_iff x e 1).1 h1

end groups

def conjugation { T: Type } [Group T] (c: T) := fun (x: T) => c * x * c⁻¹

class GroupHomomorphism (T U: Type) [Group T] [Group U] (f: T -> U) :=
map_mul : ∀ a b: T, f (a * b) = f a * f b

namespace group_homomorphism

def in_kernel {T U: Type} [Group T] [Group U] (f: T -> U) (a: T): Prop := f a = 1
def in_image {T U: Type} [Group T] [Group U] (f: T -> U) (b: U): Prop := ∃ a: T, f a = b

open groups

variable {T U: Type} [Group T] [Group U] (f: T -> U) [GroupHomomorphism T U f]

theorem map.mul : ∀ a b: T, f (a * b) = f a * f b := GroupHomomorphism.map_mul

theorem map.one : f 1 = 1 := by
  apply groups.mul.left_cancel
  show f 1 * f 1 = f 1 * 1
  rw [←GroupHomomorphism.map_mul, mul.one, mul.one]

def id := fun (x: T) => x

theorem id.homomorphism : GroupHomomorphism T T id := {
  map_mul := by intros a b; exact rfl
}

theorem conjugation.homomorphism (c: T) : GroupHomomorphism T T (conjugation c) := {
  map_mul := by
    intros a b
    unfold conjugation
    rw [
      ←mul.assoc c b,
      mul.assoc _ c,
      ←mul.assoc _ _ c,
      (Group.inverse c).left,
      mul.one,
      mul.assoc,
      mul.assoc
    ]
}

theorem homomorphism.compose { V: Type } [Group V] (f: T -> U) (g: U -> V) [GroupHomomorphism _ _ f] [GroupHomomorphism _ _ g]
  : GroupHomomorphism T V (g ∘ f) := {
    map_mul := by
      intros a b
      unfold Function.comp
      rw [←map.mul, ←map.mul]
}

theorem map.inv (a : T) : f a⁻¹ = (f a)⁻¹ := by
  apply (mul.left_cancel_iff (f a) (f a⁻¹) (f a)⁻¹).mp
  rw [←map.mul, (Group.inverse a).right, (Group.inverse (f a)).right]
  exact @map.one T U _ _ f _

theorem map.mul.inv (a b : T) : (f (a * b))⁻¹ = f b⁻¹ * f a⁻¹ := by
  rw [←map.mul, ←inv.mul, ←map.inv]

-- TODO exponents
-- theorem map_pow (a : T) (n : Natural) : f a ^ n = (f a) ^ n := by
--   induction n with
--   | zero => rw [pow.zero]
--   | successor n ih => rw [pow.successor, ih]

end group_homomorphism

namespace random

variable {T: Type} [Group T]

def are_conjugate (x x': T) : Prop := ∃g, x' = conjugation g x

open groups in
instance : Relation T are_conjugate := {
  symmetric := by
    intro a b h1
    let ⟨g, h2⟩ := h1
    apply Exists.intro (Inv.inv g)
    unfold conjugation at *
    rw [
      h2,
      inv.double,
      mul.assoc,
      ←mul.assoc _ g⁻¹ g,
      (Group.inverse g).1,
      mul.one,
      mul.assoc,
      (Group.inverse g).1,
      one.mul
    ]
  reflexivity := by
    intro a
    apply Exists.intro 1
    unfold conjugation at *
    rw [one.mul, one.inverse, mul.one]
  transitivity := by
    intro a b c h1
    let ⟨⟨g1, h2⟩, ⟨g2, h3⟩⟩ := h1
    apply Exists.intro (g2 * g1)
    unfold conjugation at *
    rw [h3, h2, inv.mul, mul.assoc, mul.assoc, mul.assoc]
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
    rw [mul_inv, mul_eq, (ga.inverse _).1, (gb.inverse _).1, mul_eq, (ga.inverse _).2, (gb.inverse _).2]
    exact ⟨one_left _ _, one_left _ _⟩
  identity := by
    intro a
    rw [mul_eq, one_left, (ga.identity _).1, (gb.identity _).1, mul_eq, (ga.identity _).2, (gb.identity _).2]
    exact ⟨rfl, rfl⟩
}

end product
