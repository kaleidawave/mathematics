import Mathematics.Structures.Set

def Set.cartesian_product {T U: Type} (s₁: Set T) (s₂: Set U): Set (T × U) := fun (l, r) => s₁ l ∧ s₂ r

instance {T U: Type} : HMul (Set T) (Set U) (Set (T × U)) := ⟨Set.cartesian_product⟩

variable (T: Type) (A B: Set T)

#check ∀ a ∈ A, sorry
