import Mathematics.Relation.PartialOrder
import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Inequality

instance : PartialOrder Natural LE.le := {
  reflexivity := by
    intro a
    unfold LE.le
    exists 0
    exact Natural.add.zero a
  antisymmetric := by
    intro a b
    unfold LE.le
    intro ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩
    rw [←h1, add.associative] at h2
    have h3 : c1 + c2 = 0 := add.left_zero_cancel a (c1 + c2) h2
    have h4 : c1 = 0 := (add.eq.zero c1 c2 h3).left
    rw [h4, Natural.add.zero] at h1
    exact h1
  transitivity := by
    intro a b c
    unfold LE.le
    intro h1
    let ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ := h1
    exists (c1 + c2)
    rw [←h1, add.associative] at h2
    exact h2
}

theorem not.le.not.equal (a b: Natural) (h1: ¬(a <= b)): a ≠ b := by
  intro h2
  rw [h2] at h1
  have h3: b <= b := PartialOrder.reflexivity b
  exact h1 h3

-- theorem Natural.eq_or_lt_of_le : {n m: Natural} → LE.le n m → Or (Eq n m) (LT.lt n m)
-- | zero,   zero,   _ => Or.inl rfl
-- | zero,   successor n, _ => by
--   right
--   induction n with
--   | zero => exact ⟨0, rfl⟩
--   | successor n ih => exact ⟨n.successor, rfl⟩
--   -- exact Natural.less_than.successor
-- | successor _, zero,   h => absurd h (Natural.less_than.zero_never _)
-- | successor n, successor m, h =>
--   have : LE.le n m := Natural.less_than.equal.successor.r _ _ h
--   match Natural.eq_or_lt_of_le this with
--   | Or.inl h => Or.inl (h ▸ rfl)
--   | Or.inr ⟨a, h⟩ => Or.inr ⟨a, by rw [successor.add, successor.pure]; exact h⟩

theorem Natural.lt_or_ge (n m : Natural) : Or (LT.lt n m) (GE.ge n m) :=
  match m with
  | zero   => Or.inr <| Natural.greater_than.equal.zero n
  | successor m =>
    match Natural.lt_or_ge n m with
    | Or.inl h => Or.inl (Natural.greater_than'.successor _ _ h)
    | Or.inr h =>
      match Natural.eq_or_lt_of_le h with
      | Or.inl h1 => Or.inl (h1 ▸ Natural.less_than.equal.self _)
      | Or.inr h1 => Or.inr h1

theorem Natural.le_total (m n : Natural) : m ≤ n ∨ n ≤ m :=
  match Natural.lt_or_ge m n with
  | Or.inl h => Or.inl (le_of_succ_le h)
  | Or.inr h => Or.inr h

theorem Natural.lt_trichotomy (m n : Natural): m < n ∨ m = n ∨ n < m :=
  match Natural.lt_or_ge m n with
  | .inl h => .inl h
  | .inr h =>
    match Natural.eq_or_lt_of_le h with
    | .inl h => .inr (.inl h.symm)
    | .inr h => .inr (.inr h)

/-- To exhibit a point -/
theorem Natural.le_total.lem (m n : Natural) : m ≤ n ∨ n ≤ m := by
  by_cases h: m <= n
  exact Or.inl h
  {
    right
    induction m generalizing n with
    | zero => sorry
    | successor m ih => {
      sorry
    }
    -- induction n generalizing m with
    -- | zero => exact Natural.greater_than.zero m
    -- | successor n ih => {
    --   exists zero.successor
    --   let d := Natural.zero_def ▸ add.zero
    --   rw [add.successor, d]
    --   clear d
    --   sorry
    -- }
  }

-- #print axioms Natural.le_total

def Natural.Min (a b: Natural) : Natural := if a <= b then a else b
instance : Min Natural := ⟨Natural.Min⟩

def Natural.Max (a b: Natural) : Natural := if a <= b then b else a
instance : Max Natural := ⟨Natural.Max⟩

-- #eval min 4 5
