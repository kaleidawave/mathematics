import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Relations

@[simp]
def Set.image_of_set { A B: Type } (f: A → B) (domain: Set A) : Set B := fun b => ∃a ∈ domain, f a = b

/-- Image over the **whole** set -/
@[simp]
def Set.image { A B: Type } (f: A → B) : Set B := Set.image_of_set f (Set.universal A)

-- TODO tidy
theorem image.intersection { A B: Type } (f: A → B) (s₁ s₂: Set A) :
  Set.image_of_set f (s₁ ∩ s₂) ⊆ ((Set.image_of_set f s₁) ∩ (Set.image_of_set f s₂)) := by
    intro b h1
    let ⟨a, ⟨⟨left, right⟩, h1⟩⟩ := h1
    exact ⟨⟨a, left, h1⟩, ⟨a, right, h1⟩⟩

theorem image.union { A B: Type } (f: A → B) (s₁ s₂: Set A) :
  Set.image_of_set f (s₁ ∪ s₂) = ((Set.image_of_set f s₁) ∪ (Set.image_of_set f s₂)) := by
    ext _
    constructor
    intro ⟨a, h1, h2⟩
    -- TODO better syntax
    exact (Or.map (fun c => ⟨a, c, h2⟩) (fun c => ⟨a, c, h2⟩) h1)

    -- TODO again better way to express this
    intro h2
    cases h2 with
    | inl h2 =>
      let ⟨a, h1⟩ := h2
      exact ⟨a, And.or_left h1⟩
    | inr h2 =>
      let ⟨a, h1⟩ := h2
      exact ⟨a, And.or_right h1⟩
