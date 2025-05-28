import Mathematics.Structures.Numbers.Natural

def Natural.add : Natural → Natural → Natural
| zero, a => a
| successor a, b => successor (add a b)

instance : Add Natural := ⟨Natural.add⟩

theorem zero.add (a: Natural) : 0 + a = a := rfl

theorem Natural.zero_add' (a: Natural) : Natural.zero + a = a := zero.add a

theorem successor.add (a b: Natural) : .successor a + b = .successor (a + b) := rfl

theorem Natural.add.zero (a: Natural) : a + 0 = a := by
  induction a with
  | zero => rfl
  | successor n n_ih => rw [successor.add, n_ih]

theorem Natural.add.zerod (a: Natural) : a + Natural.zero = a := Natural.add.zero a

theorem add.one (a: Natural) : a + 1 = .successor a := by
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

theorem add.commutative (a b: Natural) : a + b = b + a := by
  induction a with
  | zero => rw [Natural.zero_def, Natural.add.zero, zero.add]
  | successor n n_ih => rw [successor.add, add.successor, n_ih]

theorem add.associative (a b c: Natural) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rw [Natural.zero_def, Natural.add.zero, Natural.add.zero]
  | successor n n_ih => rw [add.successor, add.successor, add.successor, n_ih]

instance : Std.Commutative (α := Natural) (· + ·) := ⟨add.commutative⟩
instance : Std.Associative (α := Natural) (· + ·) := ⟨add.associative⟩
instance : Std.LawfulIdentity Natural.add 0 where
  left_id := zero.add
  right_id := Natural.add.zero

theorem add.right_cancel (a b c: Natural) : a + b = c + b ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [Natural.zero_def, Natural.add.zero, Natural.add.zero] at h1; exact h1
  | successor n ih => {
    rw [add.successor, add.successor] at h1
    exact ih (successor.inj h1)
  }
  intro h2
  rw [h2, add.commutative]

theorem add.left_cancel (a b c: Natural) : b + a = b + c ↔ a = c := by
  apply Iff.intro
  intro h1
  induction b with
  | zero => rw [←zero.add a, ←Natural.zero_def, h1, Natural.zero_def, zero.add]
  | successor n ih => {
    rw [successor.add, successor.add] at h1
    exact ih (successor.inj h1)
  }
  intro h2
  rw [h2]

-- TODO should use add.left_cancel
theorem add.left_zero_cancel (a b: Natural) : a + b = a → b = 0 := by
  intro h1
  induction a with
  | zero => rw [Natural.zero_def, zero.add] at h1; exact h1
  | successor n ih => {
    rw [successor.add] at h1
    exact ih (successor.inj h1)
  }

-- TODO should use add.left_cancel
theorem add.eq.zero (a b: Natural) : a + b = 0 → a = 0 ∧ b = 0 := by
  intro h1
  cases a with
  | zero => exact ⟨Natural.zero_def, by { rw [Natural.zero_def] at h1; exact add.left_zero_cancel _ _ h1 }⟩
  | successor n => {
    rw [successor.add] at h1
    contradiction
  }

theorem add.eq.one (a b: Natural) : a + b = 1 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  intro h1
  induction a with
  | zero => left; exact ⟨rfl, h1⟩
  | successor n ih => {
    rw [successor.add] at h1
    have b_eq := (add.eq.zero _ _ (successor.inj h1)).right
    have a_eq := Natural.add.zero _ ▸ (b_eq ▸ h1)
    exact Or.inr ⟨a_eq, b_eq⟩
  }
