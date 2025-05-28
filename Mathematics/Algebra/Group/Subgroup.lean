import Mathematics.Algebra.Group
import Mathematics.Structures.Set

class Subgroup (T: Type) [Group T] (H: Set T) where
closure: ∀a ∈ H, ∀b ∈ H, (a * b) ∈ H

-- TODO contains 0 etc

variable {T: Type} [Group T]

-- TODO name wrong
def Subgroup.unit : Subgroup T (Set.universal T) where
closure := by
  intro a _ b _
  trivial

-- TODO name wrong
def Subgroup.identity : Subgroup T (Set.singleton 1) where
closure := by
  intro a h1 b h2
  rw [h1, h2, groups.one.multiply]
  rfl
