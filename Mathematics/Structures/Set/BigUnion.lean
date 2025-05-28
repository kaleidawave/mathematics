import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Theorems

-- TODO move
-- Also copy any from https://adam.math.hhu.de/#/g/djvelleman/stg4/world/FamUnion
def BigUnion {T: Type} (U: Set (Set T)): Set T := fun x => ∃s ∈ U, x ∈ s

notation "⋃₀ " U:100 => BigUnion U

theorem BigUnion.empty {T: Type} : ⋃₀ (Set.empty (Set T)) = Set.empty T := by
  ext x
  constructor
  {
    intro ⟨_, ⟨h1, _⟩⟩
    contradiction
  }
  {
    intro h1
    contradiction
  }

theorem BigUnion.member { T: Type } (A : Set T) (F : Set (Set T)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro h2 h3
  exact ⟨A, ⟨h1, h3⟩⟩

theorem BigUnion.subset { T: Type } (F G : Set (Set T)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro h2 h3
  cases h3 with | intro w h => exact ⟨w, ⟨h1 h.left, h.right⟩⟩

theorem BigUnion.subset.iff { T: Type } (A: Set T) (F : Set (Set T)) : (⋃₀ F) ⊆ A ↔ ∀s ∈ F, s ⊆ A := by
  constructor
  {
    intro h1 S h2 u h3
    apply h1
    exact ⟨S, ⟨h2, h3⟩⟩
  }
  {
    intro h1 S ⟨w, h⟩
    exact ((h1 w) h.left) h.right
  }

-- TODO move
def Set.Pair {T: Type} (x y: T) : Set T := (Set.singleton x) ∪ (Set.singleton y)

theorem mem_pair {T: Type} (t x y: T) : t ∈ Set.Pair x y ↔ t = x ∨ t = y := by
  constructor
  intro h1; cases h1; left; assumption; right; assumption;
  intro h1; exact h1;

theorem BigUnion.union.pair { T: Type } (A B: Set T) : A ∪ B = ⋃₀ Set.Pair A B := by
  ext x
  constructor
  {
    intro h1
    cases h1 with
    | inl h1 => {
      have D: A ∈ (Set.Pair A B) := (mem_pair A _ _).mpr (Or.inl rfl)
      exact ⟨A, ⟨D, h1⟩⟩
    }
    | inr h1 => {
      have D: B ∈ (Set.Pair A B) := (mem_pair B _ _).mpr (Or.inr rfl)
      exact ⟨B, ⟨D, h1⟩⟩
    }
  }
  {
    intro h1
    have ⟨u, ⟨a, b⟩⟩ := h1
    rw [mem_pair] at a
    cases a with
    | inl h => rw [h] at b; exact Or.inl b
    | inr h => rw [h] at b; exact Or.inr b
  }

theorem BigUnion.union.union { T: Type } (F G: Set (Set T)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  constructor
  {
    intro h1
    have ⟨u, ⟨h2, h3⟩⟩ := h1
    cases h2 with
    | inl h => {
      left
      exact ⟨u, ⟨h, h3⟩⟩
    }
    | inr h => {
      right
      exact ⟨u, ⟨h, h3⟩⟩
    }
  }
  {
    intro h1
    cases h1 with
    | inl h => {
      have ⟨l, r⟩ := h
      exact ⟨l, ⟨Or.inl r.left, r.right⟩⟩
    }
    | inr h => {
      have ⟨l, r⟩ := h
      exact ⟨l, ⟨Or.inr r.left, r.right⟩⟩
    }
  }

theorem BigUnion.member.singleton_union { T: Type } (A B : Set T) : (A ∪ B) ⊆ ⋃₀ Set.Pair A B := by
  rw [BigUnion.union.pair]
  intro x h1; exact h1

theorem BigUnion.member.not { T: Type } (t₁ t₂: T) (h1: t₁ ≠ t₂): ¬(∀ (A : Set T) (F : Set (Set T)), A ⊆ ⋃₀ F → A ∈ F) := by
  intro h2
  let t₁s := Set.singleton t₁; let t₂s := Set.singleton t₂;
  let A := t₁s ∪ t₂s
  let F := Set.Pair t₁s t₂s
  have h3 := h2 A F
  have a_in_cup_f: A ⊆ (⋃₀ F) := BigUnion.member.singleton_union t₁s t₂s
  have d2 := h3 a_in_cup_f

  cases d2 with
  | inl h4 => {
    have d3 : A = t₁s := h4
    apply h1
    exact (union.singleton_thing t₁ t₂ d3).symm
  }
  | inr h4 => {
    have d3 : A = t₂s := h4
    apply h1
    have d4 := (union.singleton_thing t₂ t₁)
    have d5 : ∀a b: Set T, a ∪ b = a ∪ b := fun a b => rfl
    rw [←d5, union.symmetric] at d4
    exact d4 d3
  }
