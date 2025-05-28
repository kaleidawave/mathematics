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

theorem And.symmetric (A B: Prop) : (A ∧ B) = (B ∧ A) := by
  apply propext
  apply Iff.intro
  repeat {
    intro h1
    let ⟨left, right⟩ := h1
    exact ⟨right, left⟩
  }

theorem And.self (A: Prop) : (A ∧ A) = A := by
  apply propext
  apply Iff.intro
  exact And.left
  exact fun a => ⟨a, a⟩

theorem And.false (A: Prop) : (False ∧ A) = False := by
  apply propext
  apply Iff.intro
  exact And.left
  exact False.elim

theorem And.associative (A B C: Prop) : ((A ∧ B) ∧ C) = (A ∧ (B ∧ C)) := by
  apply propext
  constructor
  exact fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩
  exact fun ⟨a, ⟨b, c⟩⟩ => ⟨⟨a, b⟩, c⟩

-- TODO is there a simpler way to do this?
theorem Or.associative (A B C: Prop) : ((A ∨ B) ∨ C) = (A ∨ (B ∨ C)) := by
  apply propext
  constructor
  {
    intro h1
    cases h1 with
    | inl h => cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  }
  {
    intro h1
    cases h1 with
    | inl h => exact Or.inl (Or.inl h)
    | inr h => cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h
  }

theorem And.or_left { A B C: Prop } : A ∧ C → ((A ∨ B) ∧ C) := fun h1 => ⟨Or.inl h1.left, h1.right⟩
theorem And.or_right { A B C: Prop } : B ∧ C → ((A ∨ B) ∧ C) := fun h1 => ⟨Or.inr h1.left, h1.right⟩

theorem Or.false (A: Prop) : (False ∨ A) = A := by
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
  by intro h1 h2; exact h1 h2.left h2.right,
  by intro h h1 h2; exact h ⟨h1, h2⟩
⟩

theorem DeMorgan.not_or { a b : Prop } : Not (a ∨ b) ↔ Not a ∧ Not b := ⟨
  by
    intro h
    constructor
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
    intro h1 h2
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

theorem ModusTollens (p q: Prop) : (¬p → ¬q) = (q → p) := by
  apply propext
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
  exact fun _ => ModusTollens _ _

theorem Or.not_right (p q: Prop) (h1: p ∨ q) (h2: ¬q): p := by
  cases h1 with
  | inl l => exact l
  | inr r => exact (h2 r).elim

theorem Or.not_left (p q: Prop) (h1: p ∨ q) (h2: ¬p): q := by
  cases h1 with
  | inl l => exact (h2 l).elim
  | inr r => exact r

theorem Or.disjunctive_simplification (p: Prop) : (p ∨ p) = p := by
  apply propext
  constructor
  intro h; cases h with | inl h => exact h | inr h => exact h
  intro h; exact Or.inl h

example (p: Prop) : ¬(p ∧ ¬p) := fun ⟨l, r⟩ => (r l)

theorem DistributiveAnd (a b c: Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := ⟨
  by { intro h1; cases h1.left with | inl h => exact Or.inl ⟨h, h1.right⟩ | inr h => exact Or.inr ⟨h, h1.right⟩ },
  by { intro h1; cases h1 with | inl h => exact ⟨Or.inl h.left, h.right⟩ | inr h => exact ⟨Or.inr h.left, h.right⟩ }
⟩

theorem DistributiveOr (a b c: Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := ⟨
  by { intro h1; cases h1 with | inl h => exact ⟨Or.inl h.left, Or.inl h.right⟩ | inr h => exact ⟨Or.inr h, Or.inr h⟩ },
  by {
    rintro ⟨h1, h2⟩;
    cases h1 with
    | inl h => { cases h2 with | inl p => exact Or.inl ⟨h, p⟩ | inr p => exact Or.inr p }
    | inr h => { cases h2 with | inl p => exact Or.inr h | inr p => exact Or.inr p }
  }
⟩

theorem DistributiveAnd.double (a b c d: Prop) : (a ∨ b) ∧ (c ∨ d) ↔ (a ∧ c) ∨ (a ∧ d) ∨ (b ∧ c) ∨ (b ∧ d) := by
  conv =>
    lhs
    rw [DistributiveAnd]
    conv => lhs; rw [And.comm, DistributiveAnd, And.comm, @And.comm d _]
    conv => rhs; rw [And.comm, DistributiveAnd, And.comm, @And.comm d _]
  rw [Or.associative]

theorem DistributiveOr.double (a b c d: Prop) : (a ∧ b) ∨ (c ∧ d) ↔ (a ∨ c) ∧ (a ∨ d) ∧ (b ∨ c) ∧ (b ∨ d) := by
  conv =>
    lhs
    rw [DistributiveOr]
    conv => lhs; rw [Or.comm, DistributiveOr, Or.comm, @Or.comm d _]
    conv => rhs; rw [Or.comm, DistributiveOr, Or.comm, @Or.comm d _]
  rw [And.associative]

example (a b c d: Prop) : (a ∧ b ∧ c) ∨ d ↔ (a ∨ d) ∧ (b ∨ d) ∧ (c ∨ d) := by
  conv => lhs; rw [DistributiveOr, DistributiveOr]

example (a1 a2 b c d: Prop) : ((a1 ∨ a2) ∧ b ∧ c) ∨ d ↔
  ((a1 ∨ a2) ∨ d) ∧ (b ∨ d) ∧ (c ∨ d) := by
    conv => lhs; rw [DistributiveOr, DistributiveOr]

open Classical in theorem DoubleNegation (p: Prop) : ¬(¬p) ↔ p := Decidable.not_not

open Classical in theorem IffModusTollens (p q: Prop) : (¬p ↔ ¬q) ↔ (p ↔ q) := by
  constructor
  intro ⟨h1, h2⟩
  {
    constructor
    exact (ModusTollens q p).mp h2
    exact (ModusTollens p q).mp h1
  }
  intro ⟨h1, h2⟩
  {
    constructor
    intro h3
    have d := (ModusTollens (¬q) ¬p).mp
    apply d
    intro h1
    rw [DoubleNegation] at h1
    exact False.elim (h3 (h2 h1))
    exact h3
    intro h3 h4
    exact h3 (h1 h4)
  }

-- theorem NotForAll' {T: Type} (p: T → Prop): (¬∀t: T, p t) ↔ ∃t: T, ¬p t := Classical.not_forall

theorem NotForAll {T: Type} (p: T → Prop): (¬∀t: T, p t) ↔ ∃t: T, ¬p t := by
  constructor
  {
    intro h1
    sorry
  }
  {
    intro ⟨t, h1⟩ h2
    specialize h2 t
    exact h1 h2
  }

theorem NotExists {T: Type} (p: T → Prop): (∀t: T, ¬p t) ↔ ¬∃t: T, p t := by
  constructor
  {
    intro h1 ⟨t, h2⟩
    specialize h1 t
    exact h1 h2
  }
  {
    intro h1 t h2
    apply h1
    exact ⟨t, h2⟩
  }

theorem VaccousTruth (P: Prop): ∀_: Empty, P := by intro _; contradiction

theorem ForAllAnd {T: Type} (P Q: T → Prop) : (∀t: T, P t ∧ Q t) ↔ ((∀t: T, P t) ∧ ∀t: T, Q t) := by
  constructor
  intro h1;
    constructor;
    intro t; exact (h1 t).left;
    intro t; exact (h1 t).right;
  intro h1;
    intro t;
    exact ⟨h1.left t, h1.right t⟩

theorem NotForAllOr {T: Type} (P Q: T → Prop) (t: T) : ¬((∀t: T, P t ∨ Q t) → ((∀t: T, P t) ∨ ∀t: T, Q t)) := by
  intro h1
  sorry
