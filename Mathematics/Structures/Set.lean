import Mathematics.Logic

def Set (A: Type): Type := A → Prop

@[simp]
theorem Set.extensionality (s₁ s₂: Set A) : s₁ = s₂ ↔ ∀ a: A, s₁ a ↔ s₂ a := by
  apply Iff.intro
  {
   intro h1 a
   rw [h1]
   exact Iff.refl _
  }
  {
    intro h1
    funext a
    exact propext (h1 a)
  }


/-- Containing all items of a type -/
def Set.universal (A: Type) : Set A := fun _ => true

/-- Containing a single item -/
def Set.singular {A: Type} (a: A) : Set A := fun item => item = a

/-- A set with no items -/
def Set.empty (A: Type) : Set A := fun _ => false

def Set.complement {A: Type} (s: Set A) : Set A := fun item => ¬(s item)

namespace operators

variable { A: Type }

def Set.cartesian_product {A B: Type} (left: Set A) (right: Set B): Set (A × B) := fun (l, r) => left l ∧ right r

instance {A B: Type} : HMul (Set A) (Set B) (Set (A × B)) := ⟨Set.cartesian_product⟩

@[simp]
def Set.includes (z: Set A) (a: A) : Prop := z a

@[simp]
instance { A: Type }: Membership A (Set A) := ⟨fun z a => Set.includes a z⟩

@[simp]
def Set.union (s₁ s₂: Set A) : Set A := fun (a) => a ∈ s₁ ∨ a ∈ s₂

@[simp]
def Set.intersection (s₁ s₂: Set A) : Set A := fun (a) => a ∈ s₁ ∧ a ∈ s₂

-- Non strict
def Set.subset (s₁ s₂: Set A) : Prop := ∀ a: A, a ∈ s₁ → a ∈ s₂

-- Non strict
def Set.superset (s₁ s₂: Set A) : Prop := subset s₂ s₁

def Set.disjoint (s₁ s₂: Set A) : Prop := Set.intersection s₁ s₂ = Set.empty A

infix:20 " ∩ " => Set.intersection
infix:20 " ∪ " => Set.union
infix:20 " ⊆ " => Set.subset
infix:20 " ⊇ " => Set.superset
postfix:20 "ᶜ" => Set.complement
notation "∅" => Set.empty _

end operators

namespace theorems

open operators
variable { A: Type }

theorem Set.universal.includes (a: A) : a ∈ Set.universal A := rfl

theorem Set.singular.includes.self (a: A) : a ∈ Set.singular a := rfl

theorem Set.singular.includes (a b: A) : b ∈ Set.singular a ↔ a = b := by
  apply Iff.intro
  intro h1
  unfold Set.singular at h1
  rw [h1]
  intro h1
  rw [h1]
  exact Set.singular.includes.self b

theorem Set.empty.no_members' (a: A): a ∈ Set.empty A → False := by intro h1; contradiction

theorem Set.empty.no_members : ¬(∃a, a ∈ Set.empty A) := fun ⟨a, p⟩ => Set.empty.no_members' a p

theorem Set.union_is_superset (s₁ s₂: Set A) : Set.subset s₁  (Set.union s₁ s₂) := by
  unfold Set.subset Set.union
  intro a
  intro a_in_s₁
  apply Or.inl
  exact a_in_s₁

theorem Set.union.symmetric (s₁ s₂: Set A) : Set.union s₁ s₂ = Set.union s₂ s₁ := by
  funext a
  unfold Set.union
  rw [Or.symmetric]

theorem Set.complement.complement (s₁: Set A) : Set.complement (Set.complement s₁) = s₁ := by
  unfold Set.complement
  rw [Set.extensionality]
  intro h1
  apply Iff.intro
  intro h2
  sorry
  intro h2
  intro h3
  exact h3 h2

theorem Set.union_is_superset' (s₁ s₂: Set A) : Set.subset s₂ (Set.union s₁ s₂) := Set.union.symmetric s₁ s₂ ▸ Set.union_is_superset s₂ s₁

theorem Set.intersection.symmetric (s₁ s₂: Set A) : Set.intersection s₁ s₂ = Set.intersection s₂ s₁ := by
  unfold Set.intersection
  funext a
  rw [And.symmetric]

theorem Set.intersection.self (s₁: Set A) : Set.intersection s₁ s₁ = s₁ := by
  unfold Set.intersection
  funext a
  rw [And.self]
  rfl

theorem Set.intersection.empty (s₁ : Set A) : Set.intersection s₁ (Set.empty A) = Set.empty _ := by
  unfold Set.intersection
  funext a
  apply propext
  apply Iff.intro
  intro h1
  exact ((Set.empty.no_members' a) h1.right).elim
  intro h2
  exact ((Set.empty.no_members' a) h2).elim

theorem Set.intersection.universal (s₁ : Set A) : Set.intersection s₁ (Set.universal A) = s₁ := by
  unfold Set.intersection
  funext a
  apply propext
  apply Iff.intro
  intro h1
  exact h1.1
  intro h2
  exact ⟨h2, Set.universal.includes a⟩

theorem Set.union.empty (s₁: Set A) : Set.union s₁ (Set.empty A) = s₁ := by
  unfold Set.union
  funext a
  apply propext
  apply Iff.intro
  intro h1
  cases h1 with
  | inl h1 => exact h1
  | inr h1 => exact ((Set.empty.no_members' a) h1).elim
  exact Or.inl

theorem Set.disjoint.self_implies_empty (s₁: Set A) : Set.disjoint s₁ s₁ → s₁ = Set.empty A := by
  intro h1
  unfold Set.disjoint at h1
  have h2 := Set.intersection.self s₁
  exact Eq.trans h2.symm h1

theorem Set.disjoint.symmetric (s₁ s₂: Set A) : Set.disjoint s₁ s₂ = Set.disjoint s₂ s₁ := by
  unfold Set.disjoint
  rw [Set.intersection.symmetric]

theorem Set.subset.right_complement_eq_disjoint (s₁ s₂: Set A) : Set.subset s₁ (Set.complement s₂) ↔ Set.disjoint s₁ s₂ := by
  apply Iff.intro
  {
    unfold Set.disjoint
    rw [Set.extensionality]
    intros h1 a
    apply Iff.intro
    {
      intro h3
      exact False.elim (((h1 a) h3.1) h3.2)
    }
    {
      intro h2
      exact False.elim ((Set.empty.no_members' a) h2)
    }
  }
  {
    intros h1 a aInS₁ aInS₂
    have ⟨d, _⟩ := ((Set.extensionality _ _).1 h1) a
    exact (Set.empty.no_members' a) (d ⟨aInS₁, aInS₂⟩)
  }

theorem Set.subset.right_complement_eq_disjoint' (s₁ s₂: Set A) : Set.subset s₁ (Set.complement s₂) ↔ Set.disjoint s₂ s₁ := Set.disjoint.symmetric s₁ s₂ ▸ Set.subset.right_complement_eq_disjoint s₁ s₂

theorem Set.subset.left_complement_eq_subset (s₁ s₂: Set A) : Set.subset (Set.complement s₁) s₂ ↔ Set.subset s₂ (Set.complement s₁) := by
  apply Iff.intro
  {
    intro h1 a h2 n
    have d := h1 a
    sorry
  }
  {
    intro h1 a h2

    sorry
  }

theorem Set.subset.left_complement_eq_disjoint (s₁ s₂: Set A) : Set.subset (Set.complement s₁) s₂ ↔ Set.disjoint s₁ s₂ := by
  apply Iff.intro
  {
    sorry
  }
  {
    intros h1 a h2
    have ⟨d, r⟩ := ((Set.extensionality _ _).1 h1) a
    sorry
    -- have ⟨d, _⟩ := ((Set.extensionality _ _).1 h1) a
    -- exact (Set.empty.no_members' a) (d ⟨aInS₁, aInS₂⟩)
  }

end theorems

namespace image

@[simp]
def Set.image_of_set { A B: Type } (f: A → B) (domain: Set A) : Set B := fun b: B => ∃a: A, domain a ∧ f a = b

/-- Image over the **whole** set -/
@[simp]
def Set.image { A B: Type } (f: A → B) : Set B := Set.image_of_set f (Set.universal A)

-- TODO tidy
theorem Set.image.intersection { A B: Type } (f: A → B) (s₁ s₂: Set A) :
  Set.image_of_set f (s₁ ∩ s₂) ⊆ ((Set.image_of_set f s₁) ∩ (Set.image_of_set f s₂)) := by
    intro b h1
    let ⟨a, ⟨⟨left, right⟩, h1⟩⟩ := h1
    exact ⟨⟨a, left, h1⟩, ⟨a, right, h1⟩⟩

theorem Set.image.union { A B: Type } (f: A → B) (s₁ s₂: Set A) :
  Set.image_of_set f (s₁ ∪ s₂) = ((Set.image_of_set f s₁) ∪ (Set.image_of_set f s₂)) := by
    rw [Set.extensionality]
    intro b
    apply Iff.intro
    intro h1
    let ⟨a, h1, h2⟩ := h1
    -- TODO better syntax
    exact (Or.map (fun c => ⟨a, c, h2⟩) (fun c => ⟨a, c, h2⟩) h1)

    -- TODO again better way to express this
    intro h2
    cases h2 with
    | inl a =>
      let ⟨a, h1⟩ := a
      exact ⟨a, And.or_left h1⟩
    | inr a =>
      let ⟨a, h1⟩ := a
      exact ⟨a, And.or_right h1⟩

end image
