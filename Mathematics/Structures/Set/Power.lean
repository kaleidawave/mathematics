import Mathematics.Structures.Set
import Mathematics.Structures.Set.Theorems

def PowerSet {T: Type} (S: Set T): Set (Set T) := fun s => s ⊆ S

-- @[inherit_doc] prefix:100 "𝒫" => powerset

theorem PowerSet.includes.self {T: Type} (S: Set T) : S ∈ PowerSet S := fun x => subset.self x

theorem PowerSet.includes.empty {T: Type} (S: Set T) : (Set.empty T) ∈ PowerSet S
  := fun x => subset.empty x
