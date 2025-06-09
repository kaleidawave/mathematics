import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Natural.Addition

def Integer.add (a b: Integer): Integer := Quotient.lift₂
  (fun a b: NatPair => Integer.mk (a.fst + b.fst, a.snd + b.snd))
  (by
    intro (a, b) (c, d) (e, f) (g, h) h1 h2
    replace h1 : b + e = f + a := h1
    replace h2 : d + g = h + c := h2
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    -- TODO via calc
    conv => lhs; rw [
      ←Natural.add_associative,
      Natural.add_commutative b,
      Natural.add_associative d,
      h1,
      Natural.add_commutative _ g,
      Natural.add_commutative f,
    ]
    conv => rhs; rw [
      Natural.add_associative,
      Natural.add_commutative a,
      ←Natural.add_associative h,
      ←h2,
      Natural.add_commutative d,
      Natural.add_commutative f
    ]
    rw [←Natural.add_associative, ←Natural.add_associative]
  ) a b

instance : Add Integer := ⟨Integer.add⟩

theorem Integer.add_zero (a: Integer) : a + 0 = a := by
  cases a using Quotient.ind
  apply Quotient.sound
  have d : Natural.from.nat 0 = 0 := rfl
  rw [Natural.add_zero, d, Natural.add_zero]
  rfl

theorem Integer.add_commutative (a b: Integer) : a + b = b + a := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound
  rw [Natural.add_commutative]
  conv => rhs; rhs; rw [Natural.add_commutative]
  rfl

theorem Integer.add_associative (a b: Integer) : a + (b + c) = (a + b) + c := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  cases c using Quotient.ind
  apply Quotient.sound
  rw [Natural.add_associative, Natural.add_associative]
  rfl

def Integer.successor (a: Integer): Integer := a + 1
