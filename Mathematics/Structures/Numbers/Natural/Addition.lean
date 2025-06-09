import Mathematics.Structures.Numbers.Natural

def Natural.add : Natural → Natural → Natural
| zero, a => a
| successor a, b => successor (add a b)

instance : Add Natural := ⟨Natural.add⟩

theorem Natural.zero_add (a: Natural) : 0 + a = a := rfl

theorem Natural.zero_add' (a: Natural) : Natural.zero + a = a := zero_add a

theorem successor.add (a b: Natural) : .successor a + b = .successor (a + b) := rfl

theorem Natural.add_zero (a: Natural) : a + 0 = a := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem Natural.add_zerod (a: Natural) : a + Natural.zero = a := Natural.add_zero a

theorem Natural.add_one (a: Natural) : a + 1 = .successor a := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem add.two (a: Natural) : a + 2 = .successor (.successor a) := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem add.successor (a b: Natural) : a + .successor b = .successor (a + b) := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, successor.add, n_ih]

theorem add.inverse.cancel (a b c: Natural) : a = b → a + c = b + c := by
  intro h1
  induction c with
  | zero => rw [h1]
  | successor n n_ih => rw [add.successor, add.successor, n_ih]

theorem Natural.add_commutative (a b: Natural) : a + b = b + a := by
  induction a with
  | zero => rw [Natural.zero_def, Natural.add_zero, zero_add]
  | successor n n_ih => rw [successor.add, add.successor, n_ih]

theorem Natural.add_associative (a b c: Natural) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rw [Natural.zero_def, Natural.add_zero, Natural.add_zero]
  | successor n n_ih => rw [add.successor, add.successor, add.successor, n_ih]

instance : Std.Commutative (α := Natural) (· + ·) := ⟨Natural.add_commutative⟩
instance : Std.Associative (α := Natural) (· + ·) := ⟨Natural.add_associative⟩
instance : Std.LawfulIdentity Natural.add 0 where
  left_id := Natural.zero_add
  right_id := Natural.add_zero

theorem Natural.add_right_cancel (a b c: Natural) : a + b = c + b ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [Natural.zero_def, Natural.add_zero, Natural.add_zero] at h1; exact h1
  | successor n ih => {
    rw [add.successor, add.successor] at h1
    exact ih (successor.inj h1)
  }
  intro h2
  rw [h2, add_commutative]

theorem Natural.add_left_cancel (a b c: Natural) : b + a = b + c ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [←zero_add a, ←Natural.zero_def, h1, Natural.zero_def, zero_add]
  | successor n ih => {
    rw [successor.add, successor.add] at h1
    exact ih (successor.inj h1)
  }
  intro h2
  rw [h2]

-- TODO should use add.left_cancel
theorem Natural.add_left_zero_cancel (a b: Natural) : a + b = a → b = 0 := by
  intro h1
  induction a with
  | zero => rw [Natural.zero_def, zero_add] at h1; exact h1
  | successor n ih => {
    rw [successor.add] at h1
    exact ih (successor.inj h1)
  }

-- theorem add_right_zero_cancel (a b: Natural) : b + a = a → b = 0 := by
--   intro h1
--   induction a with
--   | zero => rw [Natural.zero_def, zero_add] at h1; exact h1
--   | successor n ih => {
--     rw [successor.add] at h1
--     exact ih (successor.inj h1)
--   }

-- TODO should use add.left_cancel
theorem Natural.add_eq_zero (a b: Natural) : a + b = 0 → a = 0 ∧ b = 0 := by
  intro h1
  cases a with
  | zero => exact ⟨Natural.zero_def, by { rw [Natural.zero_def] at h1; exact add_left_zero_cancel _ _ h1 }⟩
  | successor n => {
    rw [successor.add] at h1
    contradiction
  }

theorem Natural.add_eq_one (a b: Natural) : a + b = 1 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  intro h1
  induction a with
  | zero => left; exact ⟨rfl, h1⟩
  | successor n ih => {
    rw [successor.add] at h1
    have b_eq := (add_eq_zero _ _ (successor.inj h1)).right
    have a_eq := Natural.add_zero _ ▸ (b_eq ▸ h1)
    exact Or.inr ⟨a_eq, b_eq⟩
  }
