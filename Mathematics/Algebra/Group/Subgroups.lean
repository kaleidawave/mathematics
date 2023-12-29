import Mathematics.Algebra.Group
import Mathematics.Structures.Set

class Subgroup (T: Type) [Group T] (H: Set T) :=
closure: ∀ a b: T, a ∈ H ∧ b ∈ H → (a * b) ∈ H

variable {T: Type} [Group T]

-- TODO name wrong
def Subgroup.unit : Subgroup T (Set.universal T) where
closure := by
  intro a b _
  exact theorems.Set.universal.includes (a * b)

-- TODO name wrong
def Subgroup.idenity : Subgroup T (Set.singular 1) where
closure := by
  intro a b h1
  rw [theorems.Set.singular.includes, theorems.Set.singular.includes] at h1
  rw [←h1.left, ←h1.right, groups.one.multiply]
  exact theorems.Set.singular.includes.self 1

namespace coset

open image in def Group.LeftCoset (A: Type) [Group A] (a: A): Set A := Set.image (fun b => a * b)
open image def Group.RightCoset (A: Type) [Group A] (a: A): Set A := Set.image (fun b => b * a)

class Subgroup.IsNormal (T: Type) [Group T] (H: Set T) [Subgroup T H] where
  prop: Group.LeftCoset = Group.RightCoset

end coset

namespace quotient

variable (T: Type) [Group T] (H: Set T) [Subgroup T H] [coset.Subgroup.IsNormal T H]

open image def Group.Quotient : Set (Set T)
  := Set.image (fun a => coset.Group.LeftCoset T a)

-- def Group.Quotient.multiply: Group.Quotient T H → Group.Quotient T H → Group.Quotient T H := fun x y => x. * y ∈ H

end quotient
