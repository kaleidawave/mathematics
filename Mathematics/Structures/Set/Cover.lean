import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Relations

def Set.cover {T: Type} (C: Set T) (s: Set (Set T)) : Prop := ∀si ∈ s, si ⊆ C

theorem Set.cover.singleton {T: Type} (s: Set T) : Set.cover s (Set.singleton s) := by
  intro s1 h1
  rw [h1]
  exact fun _ => id
