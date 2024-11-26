import Mathematics.Structures.Numbers.Integer

def Integer.add : Integer → Integer → Integer := fun a b => ⟨
  reduce (a.val.fst + b.val.fst) (a.val.snd + b.val.snd),
  reduce.is_zero (a.val.fst + b.val.fst) (a.val.snd + b.val.snd)
⟩

instance : Add Integer := { add := Integer.add }

theorem Integer.zero_def : (0: Integer).val = (0, 0) := by rfl

-- TODO local
theorem add_def: ∀ a b: Integer, (a + b).val = reduce (a.val.fst + b.val.fst) (a.val.snd + b.val.snd) := fun _ _ => rfl

theorem Integer.add.zero (n: Integer) : n + 0 = n := by
  apply Subtype.eq
  rw [add_def, zero_def, Natural.add.zero, Natural.add.zero]
  sorry
  -- exact reduce.of_zero _ _ n.property

theorem Integer.add.commutative (n m: Integer) : n + m = m + n := by
  apply Subtype.eq
  rw [add_def, add_def, Natural.add.commutative, Natural.add.commutative m.val.fst _, Natural.add.commutative m.val.snd _]

theorem Integer.zero.add (n: Integer) : 0 + n = n := Integer.add.commutative n 0 ▸ Integer.add.zero n

theorem Integer.add.associative (a b c: Integer) : (a + b) + c = a + (b + c) := by
  apply Subtype.eq
  rw [add_def, add_def, add_def, add_def]
  rw [reduce_eq_iff]
  induction c.val.fst with
  | zero => rw [Natural.zero_def, Natural.add.zero, Natural.add.zero]; sorry
  | successor cfst ih => sorry
  -- rw [←add_def, ←add_def]
  -- have d := Prod.ext_iff.mpr ((1, 2) = (2, 1))
  /-
  cases a.property with
  | inl h1 => {
    cases b.property with
    | inl h2 => {
      have d1 := Natural.zero_def ▸ reduce.zero_right
      rw [h1, h2, Natural.zero.add, Natural.zero.add, Natural.zero.add, d1, Natural.zero.add]
      simp;
      cases c.property with
      | inl h3 => rw [h3, d1, d1, d1, Natural.add.associative];
      | inr h3 => {
        rw [h3, Natural.add.zero, Natural.add.zero];
        induction c.val.fst with
        | zero => rw [reduce.zero_right, reduce.zero_right, reduce.zero_right]
        | successor c ih => {

          sorry
        }
      }
    }
    | inr h2 => sorry
  }
  | inr h1 => sorry
  -/
  /-
  rw [add_def, add_def]
  rw [add_def, add_def]
  have d1 := Natural.zero_def.symm ▸ Natural.zero.add
  have d2 := Natural.zero_def.symm ▸ Natural.add.zero
  have d3 := Natural.zero_def.symm ▸ reduce.zero_right
  have d4 := Natural.zero_def.symm ▸ reduce.zero_right1
  cases c.property with
  | inl h1 => {
    -- c is negative
    rw [h1, Natural.add.zero, Natural.add.zero]
    induction c.val.snd with
    | zero => {
      rw [d2, d2, ←reduce.of_reduce]
      cases b.property with
      | inl h2 => rw [h2, d3, Natural.add.zero]
      | inr h2 => rw [h2, d4, Natural.add.zero]
    }
    | successor c2 ih => {
      cases b.property with
      | inl h2 => {
        -- b is negative
        rw [h2, Natural.add.zero, d3, Natural.add.zero];
        cases a.property with
        | inl h3 => {
          -- a is negative
          rw [h3, d3, d3, d3];
          simp;
          have d5 := Natural.add.associative (a.val.snd) (b.val.snd) (c2.successor);
          exact d5.symm;
        }
        | inr h3 => {
          -- a is positive
          rw [h3, Natural.zero.add, Natural.zero.add];
          simp;
          -- Can we use the induction hypothesis
          sorry
        }
      }
      | inr h2 => {
        rw [h2, Natural.zero.add, Natural.add.zero];
        sorry
      }
    }
  }
  | inr h2 => sorry
  -- induction c.val.fst with
  -- | zero => {
  --
  --   rw [d, d]
  --   induction c.val.snd with
  --   | zero => {
  --     rw [d, d, ←reduce.of_reduce]
  --     induction b.val.fst with
  --     | zero => rw [reduce.zero_right, d]
  --     | successor n ih => rw [add.successor];
  --   }
  --   | successor n ih => sorry
  -- }
  -- | successor n ih => sorry
  -/
