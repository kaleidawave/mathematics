import Mathematics.Structures.Set

@[reducible]
def Set.union { A: Type } (s₁ s₂: Set A) : Set A := fun a: A => a ∈ s₁ ∨ a ∈ s₂

@[reducible]
def Set.intersection { A: Type } (s₁ s₂: Set A) : Set A := fun a: A => a ∈ s₁ ∧ a ∈ s₂

@[reducible]
def Set.difference { A: Type } (s₁ s₂: Set A) : Set A := fun a: A => a ∈ s₁ ∧ ¬(a ∈ s₂)

instance : Union (Set A) := ⟨Set.union⟩
instance : Inter (Set A) := ⟨Set.intersection⟩
instance : SDiff (Set A) := ⟨Set.difference⟩

@[simp]
def Set.complement {A: Type} (s: Set A) : Set A := fun item => ¬(s item)

postfix:60 "ᶜ" => Set.complement
