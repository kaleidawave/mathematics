import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication

def Natural.subtraction.partial : Natural → Natural → Option Natural
  | Natural.zero, Natural.zero => some Natural.zero
  | Natural.zero, Natural.successor _ => none
  | n@ (Natural.successor _), Natural.zero => some n
  | Natural.successor n, Natural.successor m => Natural.subtraction.partial n m

def Natural.subtraction.saturating : Natural → Natural → Natural
  | Natural.zero, Natural.zero => Natural.zero
  | Natural.zero, Natural.successor _ => Natural.zero
  | n@ (Natural.successor _), Natural.zero => n
  | Natural.successor n, Natural.successor m => Natural.subtraction.saturating n m

-- def Natural.subtraction.saturating : Natural → Natural → Natural
--   := fun a b => (Natural.subtraction.partial a b).getD (Natural.zero)
notation a:60 " -ₛ " b:60 => Natural.subtraction.saturating a b

def Natural.difference (a b: Natural): Natural :=
  let s := Natural.subtraction.saturating a b
  if s = 0 then Natural.subtraction.saturating b a else s

theorem Natural.subtraction.functions_equivalent (n m: Natural): n -ₛ m = (Natural.subtraction.partial n m).getD 0 := by
  cases n
  { cases m <;> rfl }
  cases m
  rfl
  {
    have h1: ∀a b: Natural, a.successor -ₛ b.successor = a -ₛ b := fun a b => rfl
    have h2: ∀a b: Natural, Natural.subtraction.partial a.successor b.successor = Natural.subtraction.partial a b := fun a b => rfl
    rw [h1, h2]
    -- Still don't quite understand how it allows this recursion
    exact Natural.subtraction.functions_equivalent _ _
  }

-- #eval (15: Natural) -ₛ 20

-- #eval (15: Natural) < 20
-- #eval (0: Natural) -ₛ 1
-- #print Natural.subtraction.partial
-- #print Natural.subtraction.partial.eq_def

theorem subtraction.not_zero : ¬(∀ a b: Natural, a -ₛ b = 0 → a = b) := by
  intro condition
  specialize condition 3 5
  have d : (3: Natural) = 5 := condition rfl
  contradiction

theorem subtraction.rhs.zero (n: Natural): n -ₛ 0 = n := by
  induction n with
  | zero => rfl
  | successor n ih => conv => lhs; unfold Natural.subtraction.saturating;

theorem subtraction.rhs.zerod (n: Natural): n -ₛ Natural.zero = n := subtraction.rhs.zero n

theorem subtraction.lhs.zero (n: Natural) : 0 -ₛ n = 0 := by cases n <;> rfl
theorem subtraction.lhs.zerod (n: Natural) : Natural.zero -ₛ n = 0 := subtraction.lhs.zero n

theorem subtraction.lhs.successor (n: Natural) : Natural.successor n -ₛ 1 = n := by cases n <;> rfl

theorem Natural.predecessor.eq_ssub_one (n: Natural) : n -ₛ 1 = n.predecessor := by
  cases n; rfl; rw [subtraction.lhs.successor]; exact rfl

theorem subtraction.self (n: Natural) : n -ₛ n = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => unfold Natural.subtraction.saturating; exact ih

theorem subtraction.successor (n m: Natural) : n.successor -ₛ m.successor = n -ₛ m := rfl

theorem subtraction.lhs.addition (n m: Natural) : (n + m) -ₛ m = n := by
  induction m with
  | zero => {
    have d := Natural.zero_def ▸ Natural.add.zero
    rw [d]
    exact subtraction.lhs.successor n
  }
  | successor m ih => {
    conv => lhs; lhs; rw [add.successor];
    unfold Natural.subtraction.saturating
    exact ih
  }

theorem subtraction.lhs.addition' (n m: Natural) : (m + n) -ₛ m = n := by
  conv => lhs; lhs; rw [add.commutative];
  exact subtraction.lhs.addition n m

-- Build cycle
def lte (a b : Natural) : Prop := ∃c: Natural, a + c = b

theorem subtraction.lhs.addition'' (n m: Natural) (h1: lte m n) : m + (n -ₛ m) = n := by
  obtain ⟨c, h1⟩ := h1
  rw [←h1, subtraction.lhs.addition']

theorem subtraction.lhs.addition''' (n m: Natural) (h1: lte m n) : (n -ₛ m) + m = n := by
  obtain ⟨c, h1⟩ := h1
  rw [←h1, add.commutative, subtraction.lhs.addition']

-- def hmm (a b c: Natural) := ((a + b) -ₛ c, a + (b -ₛ c))
-- #eval hmm 1 2 3 -- FALSE, so cannot prove the below

-- theorem subtraction.hmm (a b c: Natural) : (a + b) -ₛ c = a + (b -ₛ c) := by
--   induction c with
--   | zero => rw [subtraction.rhs.zero, subtraction.rhs.zero]
--   | successor c ih => {
--     sorry
--   }
  -- conv => lhs; lhs; rw [add.commutative];
  -- exact subtraction.lhs.addition n m

theorem Difference.self (a: Natural): Natural.difference a a = 0 := by
  unfold Natural.difference
  rw [subtraction.self]
  rfl

theorem Difference.self_iff (a b: Natural): Natural.difference a b = 0 → a = b := by
  intro h1
  unfold Natural.difference at h1
  induction b generalizing a with
  | zero => {
    rw [subtraction.lhs.zerod, subtraction.rhs.zerod] at h1
    cases a <;> exact h1
  }
  | successor b ih => {
    cases a with
    | zero => {
      rw [subtraction.lhs.zerod, subtraction.rhs.zerod] at h1
      exact h1.symm
    }
    | successor a => {
      rw [subtraction.successor, subtraction.successor] at h1
      specialize ih a h1
      rw [ih]
    }
  }

theorem Difference.symmetric (a b: Natural): Natural.difference a b = Natural.difference b a := by
  unfold Natural.difference
  cases a with
  | zero =>
    rw [subtraction.lhs.zerod, subtraction.rhs.zerod];
    cases b <;> rfl
  | successor a => {
    cases b with
    | zero => {
      rw [subtraction.lhs.zerod, subtraction.rhs.zerod];
      rfl
    }
    | successor b => {
      rw [subtraction.successor, subtraction.successor]
      exact Difference.symmetric a b
    }
  }

theorem Difference.zero (a: Natural): Natural.difference a 0 = a := by
  unfold Natural.difference
  rw [subtraction.rhs.zero, subtraction.lhs.zero]
  cases a <;> rfl

theorem Difference.zerod (a: Natural): Natural.difference a Natural.zero = a := Difference.zero a

theorem Difference.zeror (a: Natural): Natural.difference 0 a = a := Difference.symmetric _ _ ▸ Difference.zero a
theorem Difference.zerodr (a: Natural): Natural.difference Natural.zero a = a := Difference.zeror a

theorem Difference.successor (a b: Natural): Natural.difference a.successor b.successor = Natural.difference a b := by
  cases a with
  | zero => {
    rw [Difference.zerodr]
    cases b <;> rfl
  }
  | successor a => {
    unfold Natural.difference
    rw [subtraction.successor, subtraction.successor]
  }

theorem Difference.add (a b c: Natural): Natural.difference (a + c) (b + c) = Natural.difference a b := by
  induction c with
  | zero => {
    rw [Natural.add.zerod, Natural.add.zerod]
  }
  | successor c ih => {
    rw [add.successor, add.successor, Difference.successor, ih]
  }

#eval (fun a b c d => (Natural.difference (a + c) (b + d), Natural.difference a b + Natural.difference c d)) 3 7 3 1
-- #eval (fun a b m => (Natural.difference (m * a) (m * b), m * Natural.difference a b)) 1 3 2

theorem Difference.mul (a b m: Natural): Natural.difference (m * a) (m * b) = m * Natural.difference a b := by
  sorry
  -- induction a with
  -- | zero => {
  --   rw [multiply.zerod, Difference.zerodr, Difference.zeror]
  -- }
  -- | successor a ih => {
  --   cases b with
  --   | zero => {
  --     rw [multiply.zerod, Difference.zero, Difference.zerod]
  --   }
  --   | successor b => {
  --     rw [Difference.successor]
  --   }
  --   -- induction a with
  --   -- | zero => {
  --   --   rw [multiply.zerod, Difference.zerodr, Difference.zeror]
  --   -- }
  --   -- rw [multiply.successor]
  -- }
  -- induction m with
  -- | zero => {
  --   rw [zerod.multiply, zerod.multiply, zerod.multiply, Difference.zero]
  -- }
  -- | successor m ih => {
  --   rw [successor.multiply, successor.multiply, successor.multiply]
  --   rw [←ih]

  --   sorry
  --   -- exact Difference.add (m * a) (m * b)
  -- }
