import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Subtraction

-- TODO move
theorem zero_lt_sizeOf (a : Natural) : 0 < sizeOf a := by
  cases a with
  | zero => exact Nat.zero_lt_succ 0
  | successor n =>
    simp only [Natural.successor.sizeOf_spec]
    omega

-- TODO move
theorem lt_sizeOf {a b : Natural} (a_lt_b : a < b) : sizeOf a < sizeOf b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => contradiction
    | successor n =>
      simp only [Natural.zero.sizeOf_spec, Natural.successor.sizeOf_spec, Nat.lt_add_right_iff_pos]
      exact zero_lt_sizeOf n
  | successor n ih =>
    cases b with
    | zero => {
      exact Natural.less_than.zero_never n.successor a_lt_b |>.elim
    }
    | successor m =>
      simp only [Natural.successor.sizeOf_spec, Nat.add_lt_add_iff_left]
      exact ih (Natural.less_than.equal.successor.r a_lt_b)

theorem sub_lt {n m : Natural} (h1: 0 < n) (h2: 0 < m): n -ₛ m < n := by
  cases m with
  | zero => {
    contradiction
  }
  | successor m => {
    induction n with
    | zero => contradiction
    | successor n ih => {
      rw [subtraction.successor]
      exact subtraction.less_than n m
    }
  }

theorem div_rec_lemma {x y : Natural} : 0 < y ∧ y ≤ x → x -ₛ y < x :=
  fun ⟨ypos, ylex⟩ => sub_lt (Natural.less_than.equal.trans ypos ylex) ypos

def Natural.modulo' (x y : Natural) : Natural :=
  if 0 < y ∧ y ≤ x then
    Natural.modulo' (x -ₛ y) y
  else
    x
decreasing_by
  rename_i h1
  exact lt_sizeOf <| div_rec_lemma h1

-- Copied from Nat.mod
def Natural.modulo (a n: Natural): Natural := match a with
| zero => Natural.zero
| a@(successor _) =>
  if a ≤ n -- NB: if n < m does not reduce as well as `m ≤ n`!
  then Natural.modulo' a n
  else n

instance : Mod Natural := ⟨Natural.modulo⟩

theorem ModN (n: Natural) : n % n = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => {
    change (if n.successor ≤ n.successor then n.successor.modulo' n.successor else n.successor) = 0
    have n_gt_zero: 0 < n.successor := ⟨n, rfl⟩
    have n_succ_eq: n.successor <= n.successor := by rfl
    rw [if_pos n_succ_eq]
    unfold Natural.modulo'
    rw [if_pos ⟨n_gt_zero, n_succ_eq⟩, subtraction.self]
    unfold Natural.modulo'
    have n: ¬(0 < n.successor ∧ n.successor ≤ 0) := by
      intro ⟨_, h2⟩;
      exact False.elim <| (not_successor_le_zero n) h2;

    rw [if_neg n]
  }

theorem zero.mod (n: Natural): 0 % n = 0 := rfl

theorem mod.le (a b: Natural): a % b <= b := by
  induction a with
  | zero => change 0 <= b; exact Natural.greater_than.equal.zero b
  | successor n ih => {
    sorry
  }

-- Copied from Nat
def div.inductionOn.{u}
      {motive : Natural → Natural → Sort u}
      (x y : Natural)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x -ₛ y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  if h : 0 < y ∧ y ≤ x then
    ind x y h (inductionOn (x -ₛ y) y ind base)
  else
    base x y h
decreasing_by apply lt_sizeOf; apply div_rec_lemma; assumption

-- Copied from Nat
def mod.inductionOn.{u}
      {motive : Natural → Natural → Sort u}
      (x y  : Natural)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x -ₛ y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
  div.inductionOn x y ind base

example (a b: Nat) (h1: b > 0): a % b < b :=  Nat.mod_lt a h1

#eval (fun n m => (Natural.modulo' n m, n % m)) 11 6

theorem modCore_eq_mod (n m : Natural) : Natural.modulo' n m = n % m := by
  change _ = Natural.modulo n m
  match n, m with
  | 0, m =>
    unfold Natural.modulo'
    apply if_neg
    intro ⟨hlt, hle⟩
    have b_eq : m = 0 := Natural.less_than.equal.zero m hle
    rw [b_eq] at hlt
    exact Natural.less_than.zero.zero hlt
  | x@(Natural.successor x'), m =>
    unfold Natural.modulo' Natural.modulo
    cases m with
    | zero => {
      -- dsimp
      -- conv => lhs; apply if_neg (fun ⟨h1, _⟩ => Natural.less_than.zero.zero h1)
      -- conv => rhs; apply if_neg (fun h1 => (Natural.less_than.equal.zero.zero x') h1)
      sorry
    }
    | successor m => sorry
    -- rw [Natural.modulo'.eq_def]

    -- Copying things from lean4 defs, not sure
    -- rw [Natural.modulo]
    -- refine iteInduction (fun _ => rfl) (fun h => ?false) -- cannot use `split` this early yet
    -- apply if_neg
    -- intro h1
    -- rw [if_neg]
    -- sorry
    -- sorry

    -- apply if_neg


    -- exact if_neg fun ⟨_hlt, hle⟩ => h hle

-- theorem mod_eq (x y : Natural) : x % y = if 0 < y ∧ y ≤ x then (x -ₛ y) % y else x := by
--   rw [←Nat.modCore_eq_mod, ←Nat.modCore_eq_mod, Nat.modCore_eq]

-- theorem mod_eq_of_lt {a b : Natural} (h : a < b) : a % b = a :=
--   have : (if 0 < b ∧ b ≤ a then (a -ₛ b) % b else a) = a :=
--     have h' : ¬(0 < b ∧ b ≤ a) := fun ⟨_, h₁⟩ => absurd h₁ (Nat.not_le_of_gt h)
--     if_neg h'
--   (mod_eq a b).symm ▸ this

-- theorem mod.lt (a b: Natural) (h1: b ≠ 0): a % b < b := by
--   induction a, b using mod.inductionOn with
--   | base x y h2 =>
--     have h3 : ¬ 0 < y ∨ ¬ y ≤ x := Decidable.not_and_iff_or_not.mp h2
--     replace h2 : y > 0 :=  Natural.less_than.neq_zero y h1
--     match h3 with
--     | Or.inl h3 => exact False.elim <| h3 h2
--     | Or.inr h3 =>
--       have hgt : y > x := sorry -- gt_of_not_le h3
--       have heq : x % y = x := sorry --mod_eq_of_lt hgt
--       rw [←heq] at hgt
--       exact hgt
--   | ind x y h h₂ =>
--     have ⟨_, h₁⟩ := h
--     rw [mod_eq_sub_mod h₁]
--     exact h₂ h₃

theorem mod.one (n: Natural): n % 1 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih => {
    change Natural.modulo n.successor 1 = 0
    unfold Natural.modulo

    sorry
    -- have n_succ_ge_one : 1 <= n.successor := ⟨n, rfl⟩
    -- simp
    -- rw [if_pos n_succ_ge_one]
    -- unfold Natural.modulo'
    -- rw [
    --   if_pos ⟨Natural.less_than.zero.one, n_succ_ge_one⟩,
    --   ←successor.zero_eq_one,
    --   subtraction.successor n 0,
    --   subtraction.rhs.zero
    -- ]
    -- have h2: n.modulo 1 = 0 := ih
    -- unfold Natural.modulo at h2
    -- cases n with
    -- | zero => {
    --   -- exact h2
    --   sorry
    -- }
    -- | successor n => {
    --   sorry
    -- }
    -- exact ih
    -- simp
  }

-- #eval 4 % 1
