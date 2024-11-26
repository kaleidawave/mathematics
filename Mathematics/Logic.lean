theorem Or.symmetric { A B: Prop } : (A ∨ B) = (B ∨ A) := by
  apply propext
  apply Iff.intro
  repeat {
    intro h1
    cases h1 with | inl a => exact Or.inr a | inr a => exact Or.inl a
  }

/-- Transport ? #TODO can this get it's own syntax -/
def Or.map { A B C D: Prop } (h₁: A → C) (h₂ : B → D) : (A ∨ B) → (C ∨ D)
| Or.inl a => Or.inl (h₁ a)
| Or.inr b => Or.inr (h₂ b)

-- def Or.map₂ { A B C D: Prop } (h: Prop → Prop) : (A ∨ B) → (C ∨ D)
-- | Or.inl a => Or.inl (h a)
-- | Or.inr b => Or.inr (h b)

theorem And.symmetric { A B: Prop } : (A ∧ B) = (B ∧ A) := by
  apply propext
  apply Iff.intro
  repeat {
    intro h1
    let ⟨left, right⟩ := h1
    exact ⟨right, left⟩
  }

theorem And.self { A: Prop } : (A ∧ A) = A := by
  apply propext
  apply Iff.intro
  exact And.left
  exact fun a => ⟨a, a⟩

theorem And.false { A: Prop } : (False ∧ A) = False := by
  apply propext
  apply Iff.intro
  exact And.left
  exact False.elim

theorem And.or_left { A B C: Prop } : A ∧ C → ((A ∨ B) ∧ C) := fun h1 => ⟨Or.inl h1.left, h1.right⟩
theorem And.or_right { A B C: Prop } : B ∧ C → ((A ∨ B) ∧ C) := fun h1 => ⟨Or.inr h1.left, h1.right⟩

theorem Or.false { A: Prop } : (False ∨ A) = A := by
  apply propext
  apply Iff.intro
  {
    intro h1
    cases h1 with
    | inl a => exact False.elim a
    | inr a => exact a
  }
  exact Or.inr

theorem curry { a b c: Prop } : (a → b → c) ↔ a ∧ b → c := ⟨
  by intros h1 h2; exact h1 h2.left h2.right,
  by intros h h1 h2; exact h ⟨h1, h2⟩
⟩

theorem DeMorgan.not_or { a b : Prop } : Not (a ∨ b) ↔ Not a ∧ Not b := ⟨
  by
    intro h
    apply And.intro
    intro a2
    exact h (Or.inl a2)
    intro b2
    exact h (Or.inr b2),
  by
    intro h
    intro h2
    cases h2 with
    | inl a => exact h.left a
    | inr a => exact h.right a
⟩

theorem DeMorgan.not_and { a b : Prop } : Not (a ∧ b) ↔ Not a ∨ Not b := ⟨
  by
    intro h
    by_cases h1: a
    exact .inr (h ⟨h1, ·⟩)
    exact .inl h1,
  by
    intros h1 h2
    cases h1 with
    | inl l => exact l h2.1
    | inr r => exact r h2.2
⟩

theorem ImpliesCycle { a b c: Prop } : ((a → b) ∧ (b → c) ∧ (c → a)) = ((a ↔ b) ∧ (b ↔ c) ∧ (c ↔ a)) := propext ⟨
  fun ⟨ab, bc, ca⟩ => ⟨
    ⟨ab, ca ∘ bc⟩,
    ⟨bc, ab ∘ ca⟩,
    ⟨ca, bc ∘ ab⟩
  ⟩,
  fun cycle => ⟨cycle.1.1, cycle.2.1.1, cycle.2.2.1⟩
⟩

-- TODO better name
theorem Not.not_eq_symmetric (p q: Prop) : (¬p → ¬q) = (q → p) := by
  refine propext ?_
  constructor
  {
    intro h1 h2
    by_cases p' : p
    exact p'
    exact False.elim (h1 p' h2)
  }
  {
    intro h1 h2
    by_cases q' : q
    exact False.elim (h2 (h1 q'))
    exact q'
  }

example (p q: A → Prop) : (∀ a: A, ¬(p a) → ¬(q a)) = ∀ a: A, (q a → p a) := by
  refine forall_congr ?h
  exact fun _ => Not.not_eq_symmetric _ _

example (p q: Prop) (h1: p ∨ q) (h2: ¬q): p := by
  cases h1 with
  | inl l => exact l
  | inr r => exact (h2 r).elim

example (p q: Prop) (h1: p ∨ q) (h2: ¬p): q := by
  cases h1 with
  | inl l => exact (h2 l).elim
  | inr r => exact r

example (p: Prop) : ¬(p ∧ ¬p) := fun ⟨l, r⟩ => (r l)
