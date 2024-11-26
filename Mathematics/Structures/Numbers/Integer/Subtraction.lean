import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Addition

def Integer.negate (self: Integer) : Integer := by
  let ⟨⟨a, b⟩, property⟩ := self
  exact Subtype.mk ⟨b, a⟩ (by
    cases property with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  )

def Integer.subtract : Integer → Integer → Integer := fun a b => Integer.add a (Integer.negate b)

instance : Neg Integer := { neg := Integer.negate }
instance : Sub Integer := { sub := Integer.subtract }

theorem Integer.neg_def (n: Integer) : (-n).val = (n.val.snd, n.val.fst) := rfl

-- Need add zero first
theorem Integer.sub_self (n: Integer) : n - n = 0 := by
  have sub_def: n - n = n + (-n) := by rfl
  apply Subtype.eq
  rw [sub_def, add_def, neg_def, Natural.add.commutative]
  exact reduce.self _
