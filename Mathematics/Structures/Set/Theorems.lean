/- Collection of theorems about sets -/

import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Relations

variable { A: Type }

theorem universal.includes (a: A) : a ∈ Set.universal A := trivial

theorem universal.complement : (Set.universal A)ᶜ = Set.empty _ := by simp

theorem singleton.includes.self (a: A) : a ∈ Set.singleton a := rfl

theorem singleton.includes (a b: A) : b ∈ Set.singleton a ↔ a = b := by
  constructor
  intro h1
  rw [h1]
  intro h1
  exact h1 ▸ singleton.includes.self b

theorem singleton.eq (a b: A) : Set.singleton a = Set.singleton b ↔ a = b := by
  constructor
  intro h1
  rw [Set.extensionality] at h1
  exact (h1 a).mp (rfl)
  intro h2
  ext c
  rw [h2]

theorem empty.no_members' (a: A): a ∈ Set.empty A → False := by intro h1; contradiction

theorem empty.no_members : ¬(∃a, a ∈ Set.empty A) := fun ⟨a, p⟩ => empty.no_members' a p

theorem empty.complement : (Set.empty _)ᶜ = (Set.universal A) := by simp

theorem union.symmetric (s₁ s₂: Set A) : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext a
  change s₁ a ∨ s₂ a ↔ s₂ a ∨ s₁ a
  rw [Or.symmetric]

theorem union.singleton_thing (t₁ t₂: A) : (Set.singleton t₁ ∪ Set.singleton t₂ = Set.singleton t₁) → t₂ = t₁ := by
  intro h2
  have h3 := (Set.extensionality (Set.singleton t₁ ∪ Set.singleton t₂) (Set.singleton t₁)).mp h2
  exact (h3 t₂).mp (Or.inr rfl)

theorem intersection.member (s₁ s₂: Set A) (a: A) : (s₁ ∩ s₂) a = (s₁ a ∧ s₂ a) := rfl

theorem intersection.symmetric (s₁ s₂: Set A) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  ext a
  rw [intersection.member, And.symmetric (s₁ a) (s₂ a), intersection.member]

theorem intersection.self (s₁: Set A) : s₁ ∩ s₁ = s₁ := by
  ext a
  rw [intersection.member, And.self]

theorem intersection.empty.right (s₁ : Set A) : s₁ ∩ (Set.empty A) = Set.empty _ := by
  ext a
  constructor
  exact fun h1 => ((empty.no_members' a) h1.right).elim
  exact fun h2 => ((empty.no_members' a) h2).elim

theorem intersection.empty.left (s₁ : Set A) : (Set.empty A) ∩ s₁ = Set.empty _ := by
  exact intersection.symmetric _ _ ▸ intersection.empty.right _

theorem intersection.universal (s₁ : Set A) : s₁ ∩ (Set.universal A) = s₁ := by
  ext a
  constructor
  exact fun ⟨h1, _⟩ => h1
  exact fun h2 => ⟨h2, universal.includes a⟩

theorem union.member (s₁ s₂: Set A) (a: A) : (s₁ ∪ s₂) a = (s₁ a ∨ s₂ a) := rfl

theorem union.self (s₁: Set A) : s₁ ∪ s₁ = s₁ := by
  ext a
  rw [union.member, or_self]

theorem subset.of_union (s s1 s2: Set A) (h1: s ⊆ s1): s ⊆ s1 ∪ s2 := by
  intro a h2
  left;
  exact h1 h2

theorem union.empty.left (s: Set T) : (Set.empty T) ∪ s = s := by
  ext x
  constructor; intro h1; cases h1; contradiction; assumption;
  intro h1; right; assumption;

theorem union.empty.right (s: Set T) : s ∪ (Set.empty T) = s := union.symmetric s _ ▸ union.empty.left s

-- TODO what is correct terminology here
theorem union.subset.covers (s₁ s₂: Set A) (sup: s₁ ⊆ s₂) : s₁ ∪ s₂ = s₂ := by
  ext a
  constructor
  {
    intro mem_union
    cases mem_union with
    | inl mu => exact sup mu
    | inr mu => exact mu
  }
  exact Or.inr

-- TODO what is correct terminology here
theorem intersection.subset.constracts (s₁ s₂: Set A) (sup: s₁ ⊆ s₂) : s₁ ∩ s₂ = s₁ := by
  ext a
  constructor
  intro ⟨s1, _s2⟩; exact s1
  intro s1; constructor; exact s1; exact sup s1;

theorem union_eq_intersection_then_eq (s₁ s₂: Set A) : s₁ ∪ s₂ = s₁ ∩ s₂ ↔ s₁ = s₂ := by
  constructor;
  {
    intro h1
    ext x
    have d := (Set.extensionality _ _).mp h1 x;
    constructor;
    -- TODO map
    intro h2
    exact (d.mp (Or.inl h2)).right;
    intro h2
    exact (d.mp (Or.inr h2)).left;
  }
  {
    intro h2
    rw [h2, intersection.self, union.self]
  }

theorem complement.union (s₁ s₂: Set A) : (s₁ ∪ s₂)ᶜ = (s₁ᶜ) ∩ (s₂ᶜ) := by
  rw [Set.extensionality]
  intro a
  rw [Set.complement]
  exact DeMorgan.not_or

theorem complement.intersection (s₁ s₂: Set A) : (s₁ ∩ s₂)ᶜ = (s₁ᶜ) ∪ (s₂ᶜ) := by
  rw [Set.extensionality]
  intro a
  rw [Set.complement]
  exact DeMorgan.not_and

-- Requires classical reasoning for double not
open Classical in theorem complement.complement (s: Set A) : sᶜᶜ = s := by
  ext x
  unfold Set.complement
  rw [Decidable.not_not]

theorem complement.mem (a: A) (s₁: Set A) : (a ∈ s₁ᶜ) ↔ Not (a ∈ s₁) := by constructor <;> exact id

theorem difference.self (s: Set A) : s \ s = Set.empty A := by
  ext a
  constructor
  intro ⟨h1, h2⟩; exact h2 h1
  intro h1; exact h1.elim

theorem difference_as_intersection (s₁ s₂: Set A) : s₁ \ s₂ = s₁ ∩ (s₂ᶜ) := rfl

theorem mem.intersection (a: A) (s₁ s₂: Set A) : s₁ a ∧ s₂ a ↔ a ∈ (s₁ ∩ s₂) := by rfl

theorem mem.union (a: A) (s₁ s₂: Set A) : s₁ a ∨ s₂ a ↔ a ∈ (s₁ ∪ s₂) := by rfl

theorem sub.one (s₁ s₂: Set A) : s₁ \ (s₁ ∩ s₂) = s₁ \ s₂ := by
  ext a
  constructor;
  {
    intro ⟨l, r⟩
    constructor
    exact l
    rw [←complement.mem, complement.intersection, ←mem.union] at r
    cases r with
    | inl r => exact fun _ => r l
    | inr r => exact r
  }
  {
    intro ⟨l, r⟩
    constructor
    exact l
    intro h2
    rw [←mem.intersection] at h2
    exact r h2.right
  }

theorem subset.self {s: Set A} : s ⊆ s := id

theorem subset.empty {s: Set A} : (Set.empty A) ⊆ s := by
  intro a h2
  exact False.elim (empty.no_members' a h2)

theorem subset.complement_complement (s₁ s₂: Set A) : ((s₁ᶜ) ⊆ (s₂ᶜ)) = (s₂ ⊆ s₁) := by
  refine forall_congr ?h
  exact fun _ => ModusTollens _ _

theorem subset.left_complement_eq_subset (s₁ s₂: Set A) : ((s₁ᶜ) ⊆ s₂) = (s₂ᶜ ⊆ s₁) := by
  have d := subset.complement_complement s₁ (s₂ᶜ)
  rw [complement.complement] at d
  rw [d]

theorem subset.left_complement_eq_subset' (s₁ s₂: Set A) : ((s₁ᶜ) ⊆ s₂) = ((s₂ᶜ) ⊆ s₁) := by
  have d := complement.complement _ ▸ subset.complement_complement s₁ (s₂ᶜ)
  exact d

theorem subset.left_complement_eq_subset'' (s₁ s₂: Set A) : Set.subset (s₁ᶜ) s₂ = Set.subset (s₂ᶜ) s₁ := by
  have d := complement.complement _ ▸ subset.complement_complement s₁ (s₂ᶜ)
  exact d

-- theorem subset.left_complement_eq_disjoint (s₁ s₂: Set A) : (Set.subset (s₁ᶜ) s₂) ↔ Set.disjoint s₁ s₂ := by
--   constructor
--   {
--     intro h1
--     sorry
--   }
--   {
--     intro h1 a h2
--     have ⟨d, r⟩ := ((Set.extensionality _ _).1 h1) a

--     sorry
--     -- have ⟨d, _⟩ := ((Set.extensionality _ _).1 h1) a
--     -- exact (empty.no_members' a) (d ⟨aInS₁, aInS₂⟩)
--   }

namespace disjoint

theorem disjoint.definition (s₁ s₂: Set A) : Set.disjoint s₁ s₂ = (s₁ ∩ s₂ = Set.empty _) := rfl

theorem disjoint.empty (s₁: Set A) : Set.disjoint s₁ (Set.empty A) := intersection.empty.right s₁

theorem disjoint.self_implies_empty (s₁: Set A) : Set.disjoint s₁ s₁ → s₁ = Set.empty A := by
  intro h1
  unfold Set.disjoint at h1
  have h2 := intersection.self s₁
  exact Eq.trans h2.symm h1

theorem disjoint.symmetric (s₁ s₂: Set A) : Set.disjoint s₁ s₂ = Set.disjoint s₂ s₁ := by
  rw [disjoint.definition, intersection.symmetric, disjoint.definition]

theorem disjoint.mem_neg {A : Type} (s₁ s₂ : Set A): (Set.disjoint s₁ s₂) → (∀ e: A, s₁ e → ¬(s₂ e)) := by
  intro h1 e h2 h3
  unfold Set.disjoint Set.intersection at h1
  rw [Set.extensionality] at h1
  let h4 := (h1 e).1 ⟨h2, h3⟩
  unfold Set.empty at h4
  exact h4

theorem disjoint.mem_neg' {A : Type} (s₁ s₂ : Set A): (Set.disjoint s₁ s₂) → (∀ e: A, s₂ e → ¬(s₁ e)) := by
  intro h1
  rw [disjoint.symmetric] at h1
  exact disjoint.mem_neg s₂ s₁ h1

theorem subset.right_complement_eq_disjoint (s₁ s₂: Set A) : s₁ ⊆ s₂ᶜ ↔ Set.disjoint s₁ s₂ := by
  constructor
  {
    unfold Set.disjoint
    rw [Set.extensionality]
    intro h1 a
    constructor
    {
      intro h3
      exact False.elim ((h1  h3.1) h3.2)
    }
    {
      intro h2
      exact False.elim ((empty.no_members' a) h2)
    }
  }
  {
    intro h1 a aInS₁ aInS₂
    have ⟨d, _⟩ := ((Set.extensionality _ _).1 h1) a
    exact (empty.no_members' a) (d ⟨aInS₁, aInS₂⟩)
  }

theorem subset.right_complement_eq_disjoint' (s₁ s₂: Set A) : s₁ ⊆ s₂ᶜ ↔ Set.disjoint s₂ s₁
  := disjoint.symmetric s₁ s₂ ▸ subset.right_complement_eq_disjoint s₁ s₂

end disjoint
