import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Subtraction

@[reducible]
def Natural.less_than.equal (a b : Natural) : Prop := ∃c: Natural, a + c = b

@[reducible]
def Natural.less_than (a b : Natural) : Prop := Natural.less_than.equal a.successor b

@[reducible]
instance : LE Natural := ⟨Natural.less_than.equal⟩

@[reducible]
instance : LT Natural := ⟨Natural.less_than⟩

theorem Natural.less_than.equal.zero (n : Natural) (h1: n <= 0) : n = 0 := by
  have ⟨a2, h2⟩ := h1
  exact (add.eq.zero n a2 h2).left

@[refl]
theorem Natural.less_than.equal.self (n : Natural) : n <= n := by
  exact ⟨0, Natural.add.zero n⟩

theorem Natural.less_than.def (a b : Natural) : (a < b) ↔ (Natural.successor a) <= b := by
  rfl

theorem Natural.less_than.zero_never (n : Natural) : ¬(n < 0) := by
  intro h1
  have ⟨a2, h2⟩ := h1
  rw [successor.add] at h2
  exact successor.neq.zero _ h2

theorem Natural.less_than.zero.zero : ¬((0: Natural) < 0) := zero_never 0

theorem Natural.less_than.equal.zero.zero (n: Natural) : ¬(n.successor <= 0) := by
  intro ⟨a, h1⟩
  have ⟨l, _⟩ := add.eq.zero _ _ h1
  contradiction

theorem Natural.less_than.neq_zero (n : Natural) (h1: n ≠ 0): 0 < n := by
  induction n with
  | zero => contradiction
  | successor n ih =>
    by_cases h2: n = 0
    exact ⟨n, rfl⟩
    {
      obtain ⟨m, h2⟩ := ih h2
      exists m.successor
      rw [←h2, add.successor]
    }

theorem Natural.greater_than.zero (n : Natural): 0 < n.successor := ⟨n, rfl⟩
theorem Natural.greater_than.equal.zero (n : Natural): 0 <= n := ⟨n, rfl⟩

-- Cheeky!
theorem Natural.less_than.equal.neq_one (n : Natural) (h1: n ≠ 0): 1 <= n := Natural.less_than.neq_zero n h1

theorem Natural.less_than.one (n : Natural) (h1: n < 1): n = 0 := by
  obtain ⟨c, h1⟩ := h1
  cases add.eq.one _ _ h1 with
  | inl h1 => exact successor.neq.zero _ h1.left |>.elim
  | inr h1 => exact successor.inj h1.left

theorem Natural.less_than.zero.one : (0: Natural) < 1 := ⟨0, rfl⟩

theorem Natural.less_than.equal.trans {a b c: Natural} (h1: a <= b) (h2: b <= c): a <= c := by
  obtain ⟨d, h1⟩ := h1
  obtain ⟨e, h2⟩ := h2
  exists (d + e)
  rw [←h2, ←h1, ←add.associative]

theorem Natural.less_than.equal.successor.l {n m: Natural} (h1: n <= m) : n.successor <= m.successor := by
  let ⟨w, h2⟩ := h1
  exact ⟨w, by rw [←h2, successor.add]⟩

theorem Natural.less_than.equal.successor.r {n m: Natural} (h1: n.successor <= m.successor): n <= m := by
  induction n with
  | zero => exact ⟨m, zero.add m⟩
  | successor n ih =>
    have ⟨l, h2⟩ := h1
    rw [successor.add] at h2
    exact ⟨l, successor.inj h2⟩

theorem Natural.less_than.equal.successor (n m : Natural) : n <= m ↔ n.successor <= m.successor := ⟨
  @Natural.less_than.equal.successor.l n m,
  @Natural.less_than.equal.successor.r n m,
⟩

theorem Natural.less_than.not.self (n : Natural): ¬n < n := by
  intro h1
  induction n with
  | zero => exact (Natural.less_than.zero_never Natural.zero) h1
  | successor n ih => {
    rw [Natural.less_than.def, ←Natural.less_than.equal.successor, ←Natural.less_than.def] at h1
    exact ih h1
  }

theorem Natural.less_than.equal.add {x y a b: Natural} (h1: a <= b) (h2: x <= y): x + a ≤ y + b := by
    obtain ⟨c, h1⟩ := h1; obtain ⟨d, h2⟩ := h2
    rw [←h1, ←h2]
    exists (d + c)
    rw [←add.associative, ←add.associative, add.associative x, add.commutative a d, ←add.associative]

theorem Natural.no_upper_bound : ¬(∃N: Natural, ∀n: Natural, n < N) := by
  intro ⟨N, h1⟩
  specialize h1 N
  induction N with
  | zero => exact (Natural.less_than.zero_never .zero) h1
  | successor n ih =>
    have ⟨l, h2⟩ := h1
    rw [successor.add] at h2
    have h3 : ∃l, n.successor + l = n := ⟨l, (successor.inj h2)⟩
    exact ih ((Natural.less_than.def _ _).mpr h3)

theorem Natural.greater_than.successor (n m: Natural) (h1: m <= n) : (m <= n.successor) := by
  let ⟨w, h2⟩ := h1
  exact ⟨w.successor, by rw [←h2]; exact add.successor m w⟩

theorem Natural.greater_than'.successor (n m: Natural) (h1: m < n) : (m < n.successor) := by
  let ⟨w, h2⟩ := h1
  exact ⟨w.successor, by rw [←h2, successor.add, successor.add, add.successor]⟩

theorem Natural.less_than.equal.def (a b : Natural) : (a <= b) = Natural.less_than.equal a b := rfl
theorem Natural.greater_than.equal.def (a b : Natural) : (a >= b) = Natural.less_than.equal b a := rfl
theorem Natural.greater_than.equal.iff (a b : Natural) : a >= b ↔ b <= a := ⟨id, id⟩

theorem le_of_succ_le {n m : Natural} (h1 : n.successor ≤ m) : n ≤ m := by
  let ⟨w, h2⟩ := h1
  rw [successor.add, ←add.successor] at h2
  exact ⟨w.successor, h2⟩

theorem subtraction.less_than.equal (n m: Natural) : n -ₛ m <= n := by
  induction n generalizing m with
  | zero => {
    rw [subtraction.lhs.zerod]
    exact Natural.less_than.equal.self _
  }
  | successor n ih => {
    induction m with
    | zero => {
      rw [subtraction.rhs.zerod]
    }
    | successor m ih2 => {
      conv => lhs; unfold Natural.subtraction.saturating;
      have d1 := ih m
      exact Natural.greater_than.successor _ _ d1
    }
  }

theorem subtraction.less_than (n m: Natural) : n -ₛ m < n.successor := by
  rw [Natural.less_than.def, ←Natural.less_than.equal.successor]
  exact subtraction.less_than.equal n m

theorem subtraction.zero (n: Natural) : (∀m, n -ₛ m = n) → n = 0 := by
  intro h1
  apply Classical.byContradiction
  intro h2
  let one := Natural.successor (Natural.zero)
  have d := h1 one
  cases n with
  | zero => contradiction
  | successor ns => {
    unfold Natural.subtraction.saturating at d
    rw [subtraction.rhs.zerod] at d
    exact (successor.neq.successor ns) d.symm
  }

theorem subtraction.zerod (n m: Natural) (h1: n.successor -ₛ m = 0) : n -ₛ m = 0 := by
  induction m generalizing n with
  | zero => {
    rw [subtraction.rhs.zerod] at h1;
    contradiction
  }
  | successor m ih => {
    induction n with
    | zero => {
      exact subtraction.lhs.zero _
    }
    | successor m₂ ih2 => {
      rw [subtraction.successor] at h1
      rw [subtraction.successor]
      specialize ih m₂
      exact ih h1
    }
  }

theorem le_subtraction (n m: Natural): n <= m ↔ n -ₛ m = 0 := by
  constructor
  {
    intro ⟨a, h1⟩
    rw [←h1]
    -- This statement has an effect? without it the induction n changes
    clear h1

    induction n with
    | zero => exact subtraction.lhs.zero _
    | successor n ih => {
      rw [successor.add, subtraction.successor]
      exact ih
    }
  }
  {
    intro h1
    induction n generalizing m with
    | zero => exact ⟨m, by rw [Natural.zero_def, zero.add m];⟩
    | successor n2 ih => {
      induction m with
      | zero => {
        have h2 : n2.successor = Natural.zero := h1
        rw [h2]
      }
      | successor m ih2 => {
        have d: n2 -ₛ m = 0 := h1
        suffices n2 <= m by {
          have ⟨a, b⟩ := this
          exists a
          rw [←b]
          exact successor.add _ _
        }
        exact ih _ d
      }
    }
  }

instance (a b : Natural) : Decidable (a <= b) := decidable_of_iff (a -ₛ b = 0) (le_subtraction a b).symm

instance (a b : Natural) : Decidable (a < b) := by
  rw [Natural.less_than.def]
  infer_instance

theorem not_successor_le_zero (n: Natural) : ¬(n.successor) <= 0 := by
  intro h1
  exact successor.neq.zero n (Natural.less_than.equal.zero n.successor h1)

theorem Natural.eq_or_lt_of_le : {n m: Natural} → LE.le n m → Or (Eq n m) (LT.lt n m)
  | zero,   zero,        _ => Or.inl rfl
  | zero,   successor _, _ => Or.inr ((Natural.less_than.equal.successor _ _).mp (greater_than.equal.zero _))
  | successor _, zero,   h => absurd h (not_successor_le_zero _)
  | successor n, successor m, h =>
    have : LE.le n m := (Natural.less_than.equal.successor _ _).mpr h
    match Natural.eq_or_lt_of_le this with
    | Or.inl h => Or.inl (h ▸ rfl)
    | Or.inr h => Or.inr ((Natural.less_than.equal.successor _ _).mp h)

instance : WellFoundedRelation Natural where
  rel := LT.lt
  wf := by
    apply WellFounded.intro
    intro n
    induction n with
    | zero      =>
      apply Acc.intro 0
      intro _ h
      apply absurd h (Natural.less_than.zero_never _)
    | successor n ih =>
      apply Acc.intro (n.successor)
      intro m h
      have d: m <= n :=  (Natural.less_than.equal.successor m n).mpr h
      have : m = n ∨ m < n := Natural.eq_or_lt_of_le d
      match this with
      | Or.inl e => subst e; assumption
      | Or.inr e => exact Acc.inv ih e

-- #eval (2: Natural) <= 5
-- #eval ((2: Natural) < 5)
