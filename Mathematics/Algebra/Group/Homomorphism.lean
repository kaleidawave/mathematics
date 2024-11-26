import Mathematics.Algebra.Group

class GroupHomomorphism (T U: Type) [Group T] [Group U] (f: T -> U) :=
map_mul : ∀ a b: T, f (a * b) = f a * f b

def in_kernel {T U: Type} [Group T] [Group U] (f: T -> U) (a: T): Prop := f a = 1
def in_image {T U: Type} [Group T] [Group U] (f: T -> U) (b: U): Prop := ∃ a: T, f a = b

open groups

variable {T U: Type} [Group T] [Group U] (f: T -> U) [GroupHomomorphism T U f]

theorem map.multiply : ∀ a b: T, f (a * b) = f a * f b := GroupHomomorphism.map_mul

theorem map.one : f 1 = 1 := by
  apply groups.multiply.left_cancel
  show f 1 * f 1 = f 1 * 1
  rw [←GroupHomomorphism.map_mul, multiply.one, multiply.one]

-- def id := fun (x: T) => x

instance : GroupHomomorphism T T id := {
  map_mul := by intros a b; exact rfl
}

instance (c: T) : GroupHomomorphism T T (conjugation c) := {
  map_mul := by
    intros a b
    unfold conjugation
    rw [
      ←multiply.associative c b,
      multiply.associative _ c,
      ←multiply.associative _ _ c,
      (Group.inverse c).left,
      multiply.one,
      multiply.associative,
      multiply.associative
    ]
}

instance homomorphism.compose { V: Type } [Group V] (f: T -> U) (g: U -> V) [GroupHomomorphism _ _ f] [GroupHomomorphism _ _ g]
  : GroupHomomorphism T V (g ∘ f) := {
    map_mul := by
      intros a b
      unfold Function.comp
      rw [←map.multiply, ←map.multiply]
}

theorem map.inverse (a : T) : f a⁻¹ = (f a)⁻¹ := by
  apply (multiply.left_cancel_iff (f a) (f a⁻¹) (f a)⁻¹).mp
  rw [←map.multiply, (Group.inverse a).right, (Group.inverse (f a)).right]
  exact @map.one T U _ _ f _

theorem map.multiply.inverse (a b : T) : (f (a * b))⁻¹ = f b⁻¹ * f a⁻¹ := by
  rw [←map.multiply, ←inv.multiply, ←map.inverse]

-- TODO exponents
-- theorem map_pow (a : T) (n : Natural) : f a ^ n = (f a) ^ n := by
--   induction n with
--   | zero => rw [power.zero]
--   | successor n ih => rw [power.successor, ih]

def AutomorphismOf (T: Type) [Group T] := GroupHomomorphism T T
