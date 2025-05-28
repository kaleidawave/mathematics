import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Inequality

-- def Natural.pred : Natural → Natural
-- | zero => Natural.zero
-- | successor n => n

-- theorem Natural.Nat.pred (n: Natural) : Natural.to.nat n.pred = (Natural.to.nat n).pred := by cases n <;> rfl
-- theorem Natural.Nat.successor (n: Natural) : Natural.to.nat n.successor = (Natural.to.nat n).succ := by cases n <;> rfl
-- theorem Natural.Nat.eq (n: Natural) : n = 0 ↔ (Natural.to.nat n) = 0 := by
--   constructor
--   intro h1; cases n; rfl; rw [h1];
--   intro h1; cases n; rfl; rw [Natural.Nat.successor] at h1; contradiction;

-- theorem Natural.Nat.neq (n: Natural) : ¬(n = 0) → ¬(Natural.to.nat n) = 0 := by
--   intro h1 h2;
--   apply h1;
--   exact (Natural.Nat.eq n).mpr h2

theorem Nat.lt.pre (m: Nat) (h1: m ≠ 0) : m.pred < m := pred_lt h1

-- #eval (5: Natural).pred

-- theorem decreasing (n: Natural) (h1: n.pred < n) : sizeOf n.pred < sizeOf n := by
--   simp
  -- apply?
  -- sorry
-- theorem decreasing (n: Natural) (h1: ¬n = 0) : sizeOf n.pred < sizeOf n := by
  -- apply?
  -- suffices (Natural.to.nat n.pred < Natural.to.nat n) by assumption
  -- rw [Natural.Nat.pred]
  -- have neq_nat := Natural.Nat.neq n h1
  -- exact Nat.lt.pre (Natural.to.nat n) neq_nat

theorem Natural.less_than_pred (n: Natural) (h1: n ≠ 0) : n.predecessor < n := by
  induction n with
  | zero => contradiction
  | successor n ih => {
    rw [successor.predecessor]
    exact ⟨0, by rw [add.zero]⟩
  }

def N2 (a n: Natural) : Option Natural :=
  if a = 0
    then none
  else
    if a * a = n
    then
      some a
    else
      N2 (Natural.predecessor a) n
  termination_by
    match a with
    | Natural.zero => a
    | Natural.successor n => a
    exact?

def root (n: Natural) : Option Natural := N2 n n

-- theorem root_t (n: Natural)

-- #eval root 36

-- def Natural.sqrt_naive (n: Natural): Option Natural :=
  -- let rec inner :=
