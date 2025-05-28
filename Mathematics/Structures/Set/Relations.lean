import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations

variable { X: Type }

-- Non strict
@[reducible]
def Set.subset (s₁ s₂: Set X) : Prop := ∀ {a: X}, a ∈ s₁ → a ∈ s₂
-- Non strict

@[reducible]
def Set.subset.strict (s₁ s₂: Set X) : Prop := s₁ ≠ s₂ ∧ Set.subset s₁ s₂

-- Non strict
@[reducible]
def Set.superset (s₁ s₂: Set X) : Prop := subset s₂ s₁

@[reducible]
def Set.disjoint (s₁ s₂: Set X) : Prop := Set.intersection s₁ s₂ = Set.empty X

instance : HasSubset (Set X) := ⟨Set.subset⟩

instance : HasSSubset (Set X) := ⟨Set.subset.strict⟩
