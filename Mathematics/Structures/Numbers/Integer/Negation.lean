import Mathematics.Structures.Numbers.Integer

def Integer.negate (int: Integer): Integer := Quotient.lift
  (fun p: NatPair => Integer.mk (p.snd, p.fst))
  (by
    intro x y h1
    have d: x.snd + y.fst = y.snd + x.fst := h1
    apply Quotient.sound
    change PairEq (x.snd, x.fst) (y.snd, y.fst)
    simp
    rw [Natural.add_commutative x.fst, Natural.add_commutative y.fst]
    exact d.symm
  ) int

instance : Neg Integer := ⟨Integer.negate⟩

theorem Integer.neg.neg (n: Integer) : -(-n) = n := by
  cases n using Quotient.ind
  apply Quotient.sound
  rfl

theorem Integer.left_right2 (i: Integer): ∃n: Natural, i = n ∨ i = -n := Integer.left_right i
