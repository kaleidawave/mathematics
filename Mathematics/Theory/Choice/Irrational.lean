import Mathematics.Structures.Set
import Mathematics.Structures.Set.Relations
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Builder
import Mathematics.Structures.Set.Theorems

-- TODO automate
theorem union.associative (T: Type) (A B C: Set T): A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  ext x
  constructor
  . intro h1
    cases h1 with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h1 => cases h1 with
      | inl h1 => exact Or.inl (Or.inr h1)
      | inr h1 => exact Or.inr h1
  . intro h1
    cases h1 with
    | inl h1 => cases h1 with
      | inl h1 => exact Or.inl h1
      | inr h1 => exact Or.inr (Or.inl h1)
    | inr h1 => exact Or.inr (Or.inr h1)

-- theorem union2.associative (T: Type) (A B C: Set T): A.union (B.union C) = (A.union B).union C := by
--   ext x
--   constructor
--   . intro h1
--     cases h1 with
--     | inl h1 => exact Or.inl (Or.inl h1)
--     | inr h1 => cases h1 with
--       | inl h1 => exact Or.inl (Or.inr h1)
--       | inr h1 => exact Or.inr h1
--   . intro h1
--     cases h1 with
--     | inl h1 => cases h1 with
--       | inl h1 => exact Or.inl h1
--       | inr h1 => exact Or.inr (Or.inl h1)
--     | inr h1 => exact Or.inr (Or.inr h1)

instance {T: Type}: Std.Associative (α := Set T) (Set.union) := ⟨fun a b c => (union.associative T a b c).symm⟩

instance : Std.Commutative (α := Set T) (Set.union) := ⟨union.symmetric⟩

-- def Menu (T: Type): Type := Set T

-- Subtype such that codomain is subset of domain?
def Choice {T: Type}: Type := Set T -> Set T

--- Sen's alpha property.
--- Given a choice on a larger menu. Removing items (strict subset?) results in a disjoint choice?
--- examples: ABC -> C, BC -> B
--- examples: ABC -> AB, AB -> A
--- non-examples: ABC -> C, AB -> A
def Condition.Contradiction {T: Type} (c: @Choice T): Prop :=
  ∃m: Set T, ∃r: T, c (m \ Set.singleton r) ≠ ((c m) \ Set.singleton r)

inductive Alphabet where
  | A : Alphabet
  | B : Alphabet
  | C : Alphabet

variable (c: @Choice Alphabet)

def A := Alphabet.A
def B := Alphabet.B
def C := Alphabet.C

theorem a_neq_b: (A) ≠ B := Alphabet.noConfusion
theorem a_neq_c: (A) ≠ C := Alphabet.noConfusion
theorem b_neq_c: (B) ≠ C := Alphabet.noConfusion

theorem union.difference (s: Set Alphabet) (x: Alphabet) (h1: x ∉ s): (s ∪ s{x}) \ s{x} = s := by
  ext x
  constructor
  . intro ⟨h1, h2⟩
    cases h1 with
    | inl h1 => exact h1
    | inr h1 => contradiction
  . intro h1
    constructor
    exact Or.inl h1
    intro h2
    rw [h2] at h1
    contradiction

theorem difference.no_effect: (s{C}: Set Alphabet) \ s{A} = s{C} := by
  ext α
  constructor
  . intro ⟨h1, h2⟩
    exact h1
  . intro h1
    constructor
    . exact h1
    . intro h2
      rw [h2] at h1
      exact a_neq_c h1

-- If
example
  (h1: c s{A, B, C} = s{C})
  (h2: c s{B, C} = s{B})
: Condition.Contradiction c := by
  apply Exists.intro s{A, B, C}
  apply Exists.intro A

  have abc_sub_a: (s{A, B, C}: Set Alphabet) \ s{A} = s{B, C} := by
    let x := s{B, C}

    have alt_def: s{A, B, C} = x.union s{A} := by
      unfold x
      ac_nf

    have a_not_in_x: A ∉ x := by
      intro h1
      -- cases h1 <;> exact Alphabet.noConfusion h1
      cases h1 with
      | inl h1 => exact Alphabet.noConfusion h1
      | inr h1 => exact Alphabet.noConfusion h1

    have d2: x.union (Set.singleton A) \ Set.singleton A = _ := union.difference x A a_not_in_x

    rw [alt_def, d2]

  rw [h1, abc_sub_a, h2]
  intro h3
  rw [difference.no_effect, singleton.eq] at h3
  exact b_neq_c h3
