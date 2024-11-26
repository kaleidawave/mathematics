import Mathematics.Algebra.PartialOrder
import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition

def Natural.less_than.equal (a b : Natural) : Prop := ∃c: Natural, a + c = b

def Natural.less_than.equal' : Natural → Natural → Bool
| .successor n, .successor m => Natural.less_than.equal' n m
| .successor _, .zero => false
| .zero, .successor _ => true
| .zero, .zero => true

instance : LE Natural := ⟨Natural.less_than.equal⟩

instance : LT Natural where
  lt := fun a b => Natural.successor a <= b

theorem Natural.less_than.equal.zero (n : Natural) (h1: n <= 0) : n = 0 := by
  have ⟨a2, h2⟩ := h1
  exact (sum_eq_zero_implies_either_zero n a2 h2).left

theorem Natural.less_than.equal.self (n : Natural) : n <= n := by
  exact ⟨0, Natural.add.zero n⟩

theorem Natural.less_than.def (a b : Natural) : (a < b) ↔ (Natural.successor a) <= b := by
  unfold LT.lt
  rfl

theorem Natural.less_than.zero_never (n : Natural) : ¬(n < 0) := by
  intro h1
  have ⟨a2, h2⟩ := h1
  rw [successor.add] at h2
  exact successor.neq.zero _ h2

theorem Natural.greater_than.zero (n : Natural) : 0 <= n := ⟨n, rfl⟩
theorem Natural.greater_than.successor (n m: Natural) (h1: m <= n) : (m <= n.successor) := by
  let ⟨w, h2⟩ := h1
  exact ⟨w.successor, by rw [←h2]; exact add.successor m w⟩

theorem Natural.greater_than'.successor (n m: Natural) (h1: m < n) : (m < n.successor) := by
  let ⟨w, h2⟩ := h1
  exact ⟨w.successor, by rw [←h2, successor.add, successor.add, add.successor]⟩

theorem Natural.less_than.equal.def (a b : Natural) : (a <= b) = Natural.less_than.equal a b := rfl

theorem Natural.less_than.equal.successor (a b : Natural) (h1: a <= b) : a.successor<= b.successor := by
  let ⟨w, h2⟩ := h1
  exact ⟨w, by rw [←h2, successor.add]⟩

theorem Natural.less_than.equal.successor₂ (a b : Natural) (h1: a.successor <= b.successor) : a <= b := by
  let ⟨w, h2⟩ := h1
  exact ⟨w, by rw [successor.add] at h2; exact successor.inj h2⟩

/- Relates less than defintion with function -/
theorem Natural.less_than.equal.iff (a b : Natural) :
    Natural.less_than.equal a b ↔ Natural.less_than.equal' a b := by
  induction a generalizing b
  · cases b
    · simp [Natural.less_than.equal, Natural.less_than.equal']
      exists .zero
    next b' =>
      simp [Natural.less_than.equal, Natural.less_than.equal']
      exists .successor b'
  next a' ih =>
    cases b
    · simp [Natural.less_than.equal, Natural.less_than.equal', successor.add]
    next b' =>
      simp [Natural.less_than.equal, Natural.less_than.equal', ← ih, successor.add]

instance (a b : Natural) : Decidable (a <= b) := by
  rw [Natural.less_than.equal.def, Natural.less_than.equal.iff a b]
  infer_instance

instance (a b : Natural) : Decidable (a < b) := by
  rw [Natural.less_than.def]
  infer_instance

instance : PartialOrder Natural LE.le := {
  reflexivity := by
    intro a
    unfold LE.le
    exists 0
    exact Natural.add.zero a
  antisymmetric := by
    intro a b
    unfold LE.le
    intro h1
    let ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ := h1
    rw [←h1, ←Natural.add.associative] at h2
    have h3 : c1 + c2 = 0 := add.left_zero_cancel a (c1 + c2) h2
    have h4 : c1 = 0 := (sum_eq_zero_implies_either_zero c1 c2 h3).left
    rw [h4, Natural.add.zero] at h1
    exact h1
  transitivity := by
    intro a b c
    unfold LE.le
    intro h1
    let ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ := h1
    apply Exists.intro (c1 + c2)
    rw [←h1, ←Natural.add.associative] at h2
    exact h2
}

theorem not.le.not.equal (a b: Natural) (h1: ¬(a <= b)): a ≠ b := by
  intro h2
  rw [h2] at h1
  have h3: b <= b := PartialOrder.reflexivity b
  exact h1 h3

theorem Natural.eq_or_lt_of_le : {n m: Natural} → LE.le n m → Or (Eq n m) (LT.lt n m)
| zero,   zero,   _ => Or.inl rfl
| zero,   successor n, _ => Or.inr (Natural.less_than.equal.successor _ _ (Natural.greater_than.zero n))
| successor _, zero,   h => absurd h (Natural.less_than.zero_never _)
| successor n, successor m, h =>
  have : LE.le n m := Natural.less_than.equal.successor₂ _ _ h
  match Natural.eq_or_lt_of_le this with
  | Or.inl h => Or.inl (h ▸ rfl)
  | Or.inr h => Or.inr (Natural.less_than.equal.successor _ _ h)

theorem Natural.lt_or_ge (n m : Natural) : Or (LT.lt n m) (GE.ge n m) :=
  match m with
  | zero   => Or.inr (Natural.greater_than.zero n)
  | successor m =>
    match Natural.lt_or_ge n m with
    | Or.inl h => Or.inl (Natural.greater_than'.successor _ _ h)
    | Or.inr h =>
      match Natural.eq_or_lt_of_le h with
      | Or.inl h1 => Or.inl (h1 ▸ Natural.less_than.equal.self _)
      | Or.inr h1 => Or.inr h1

theorem le_of_succ_le {n m : Natural} (h1 : n.successor ≤ m) : n ≤ m := by
  let ⟨w, h2⟩ := h1
  rw [successor.add, ←add.successor] at h2
  exact ⟨w.successor, h2⟩

theorem Natural.le_total (m n : Natural) : m ≤ n ∨ n ≤ m :=
  match Natural.lt_or_ge m n with
  | Or.inl h => Or.inl (le_of_succ_le h)
  | Or.inr h => Or.inr h
