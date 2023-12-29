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

theorem dm1 { a b : Prop } : Not (a ∨ b) ↔ Not a ∧ Not b := ⟨
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
