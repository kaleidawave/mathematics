import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Inequality

def Natural.saturating_subtraction : Natural → Natural → Natural
  | .successor n1, .successor n2 => Natural.saturating_subtraction n1 n2
  | 0, .successor _ => 0
  | .successor n1, 0 => .successor n1
  | 0, 0 => 0

infix:100 " -ˢ " => Natural.saturating_subtraction

-- rwa doesn't work here for some reason
theorem subtract_self (n: Natural) : n -ˢ n = 0 := by induction n <;> rw [Natural.saturating_subtraction]; assumption

theorem subtract.succ.succ (n m: Natural) : .successor n -ˢ .successor m = n -ˢ m := rfl
theorem subtract.zero (n: Natural) : n -ˢ 0 = n := by cases n <;> rfl
theorem subtract.zero₂ (n: Natural) : 0 -ˢ n = 0 := by cases n <;> rfl

theorem add_sub_add_right (n k m : Natural) : (n + k) -ˢ (m + k) = n -ˢ m := by
  induction k with
  | zero => rw [Natural.zero_def, Natural.add.zero, Natural.add.zero]
  | successor k ih => rwa [add.successor, add.successor, subtract.succ.succ]

theorem add_sub_add_left (k n m : Natural) : (k + n) -ˢ (k + m) = n -ˢ m := by
  rw [Natural.add.commutative k n, Natural.add.commutative k m, add_sub_add_right]

theorem add_sub_cancel_left (n m : Natural) : (n + m) -ˢ n = m :=
  suffices (n + m) -ˢ (n + 0) = m by rw [Natural.add.zero] at this; assumption;
  by rw [add_sub_add_left n m 0, subtract.zero]

theorem eq_zero (a b: Natural) : a -ˢ b = 0 → ∃n: Natural, a + n = b := by
  intro h1
  induction b generalizing a with
  | zero => rw [Natural.zero_def, subtract.zero] at h1; rw [h1]; exact ⟨0, Natural.add.zero 0⟩
  | successor b ih => {
    cases a  with
    | zero => exact ⟨b.successor, Natural.zero.add _⟩
    | successor a => {
      rw [subtract.succ.succ] at h1
      have ⟨c, ih3⟩ := (ih a) h1
      exact ⟨c, by rw [successor.add, ih3]⟩
    }
  }

theorem eq_zero₂ (a b: Natural) : (∃n: Natural, a + n = b) → a -ˢ b = 0 := by
  intro ⟨c, h2⟩
  have x := subtract.zero₂ c ▸ Natural.add.zero a ▸ (add_sub_add_left a 0 c)
  exact h2 ▸ x

theorem eq_zero₃ (a b: Natural) : (∃n: Natural, a + n = b) ↔ a -ˢ b = 0 := ⟨eq_zero₂ a b, eq_zero a b⟩

theorem eq_sub (a b n: Natural) : a -ˢ b = n → b + n = a := by
  intro h1
  rw [←h1]
  sorry

-- #eval X 1 2
-- #eval X 3 2
-- #eval X 3 8
-- #eval X 5 2

theorem not.add_sub_associative : ¬(∀n m : Natural, (n + m) -ˢ n = n + (m -ˢ n)) := by
  intro h1
  specialize h1 5 2
  contradiction

theorem sub.symmetric_cancel (a b: Natural) (h1: a -ˢ b = 0) (h2: b -ˢ a = 0): a = b := by
  cases b with
  | zero => {
    rwa [Natural.zero_def, subtract.zero] at h1
  }
  | successor b => {
    have ⟨n, h3⟩ := eq_zero _ _ h1
    rw [←h3, add_sub_cancel_left] at h2
    rwa [h2, Natural.add.zero] at h3
  }

-- def x (a b c: Natural) := (a -ˢ b, c -ˢ a, b == c)
-- #eval x 3 3 3
-- #eval x 6 3 3

theorem sub.symmetric_cancel₂ (a b c: Natural) (h1: a -ˢ b = 0) (h2: c -ˢ a = 0): b = c := by
  induction b with
  | zero => {
    rw [Natural.zero_def, subtract.zero] at h1
    rw [h1, subtract.zero] at h2
    exact Natural.zero_def ▸ h2.symm
  }
  | successor b ih => {
    have ⟨n, h3⟩ := eq_zero _ _ h1
    have h6 := eq_zero _ _ h2
    rw [←h3]
    -- induction a with
    -- | zero =>  sorry
    -- | successor a ih =>  sorry
    sorry
  }
  -- induction b with
  -- | zero => {
  --   -- have x :=
  --   sorry
  -- }
  -- | successor a ih =>
  -- sorry

theorem sub (a b c: Natural) (hb : a <= b) (hc : a <= c) (h : b -ˢ a = c -ˢ a): b = c := by
  have ⟨n, h1⟩ := hb
  have ⟨m, h2⟩ := hc
  rw [←h1, ←h2, add_sub_cancel_left, add_sub_cancel_left] at h
  rw [h, h2] at h1
  exact h1.symm

theorem sub₂ (a b c : Natural) (hb : a ≤ b) (hc : c ≤ a) (h : 0 = a -ˢ c ∧ b -ˢ a = 0) : b = c := by
  have d := eq_zero₂ a b hb
  have d2 := eq_zero₂ c a hc
  sorry
  -- rw [eq_zero a b hb] at h
  -- sorry

-- -- Need
-- theorem sub₂ (a b c: Natural) (hb : a <= b) (hc : a <= c) (h : a -ˢ b = 0 ∧ 0 = c -ˢ a): b = c := by
--   have ⟨n, h1⟩ := hb
--   have ⟨m, h2⟩ := hc
--   -- rw [←h1, ←h2]

--   have ⟨_, hr⟩ := h
--   -- have ⟨n2, hmm⟩ := eq_zero _ _ hl
--   have ⟨n3, hmm₂⟩ := eq_zero _ _ hr.symm

--   rw [←h1, ←h2, add.right_cancel]
--   rw [←hmm₂, ←Natural.add.associative] at h2
--   sorry
  -- have d := (add.right_cancel (n3 + m) c 0).mp h2

  -- rw [←h1]
  -- rw [] at hl
  -- exact ⟨n, h1⟩
  -- have hr := Eq.symm hr

-- TODO
-- example (a b c: Natural) (h : b -ˢ a = c -ˢ a): b = c := by
--   sorry
  -- induction a with
  -- | zero => rw [Natural.zero_def, subtract.zero, subtract.zero] at h; exact h;
  -- | successor a ih => {
  --   apply ih
  --   induction b with
  --   | zero => sorry
  --   | successor b ih => sorry
  -- }
