import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Relations

def IsPartition {T: Type} (A B X: Set T): Prop := (A ∪ B) = X ∧ Set.disjoint A B

theorem IsPartition.set_def {T: Type} (A B X: Set T): IsPartition A B X = ((A ∪ B) = X ∧ (A ∩ B) = Set.empty T) := rfl
