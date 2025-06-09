import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Subtraction
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Ordering
import Mathematics.Structures.Numbers.Natural.Multiplication

def NatPair : Type := Natural × Natural

instance : Coe NatPair (Natural × Natural) := ⟨id⟩
instance : Coe (Natural × Natural) NatPair := ⟨id⟩

-- b - a := (b, a), d - c := (d, c). Thus b - a = d - c ↔ a + d = c + b (by rearranging)
@[reducible, simp]
def PairEq : NatPair → NatPair → Prop := fun (b, a) (d, c) => a + d = c + b

def PairEq.equivalence : Equivalence PairEq where
  refl := by intro x; rfl
  symm := by
    intro x y h1
    exact h1.symm
  trans := by
    intro x y z h1 h2
    have add_eq {a b c d: Natural} (h1: a = b) (h2: c = d) : a + c = b + d := by rw [h1, h2]
    have h3 := add_eq h1 h2
    suffices y.fst + y.snd + _ = y.fst + y.snd + _ from Natural.add_left_cancel (x.snd + z.fst) _ _ |>.mp this
    ac_nf at h3 |-
    -- rw [ add_commutative y.snd x.fst, add_commutative z.snd y.fst, ←add_associative, ←add_associative, add_associative x.snd, add_commutative y.fst y.snd, add_associative x.fst, add_associative x.fst, add_commutative _ z.snd, ←add_associative, add_associative _ y.snd _, add_associative, add_commutative _ z.fst, ←add_associative, ←add_associative x.fst, add_commutative x.fst ] at h3

instance : Setoid NatPair where
  r := PairEq
  iseqv := PairEq.equivalence

def Setoid.NatPair : Setoid NatPair := inferInstance

@[reducible]
def Integer : Type := Quotient (Setoid.NatPair)

def Integer.mk (a: Natural × Natural) : Integer := Quot.mk PairEq a

instance (p q : NatPair) : Decidable (p ≈ q) := match p, q with
  | (a, b), (c, d) => inferInstanceAs <| Decidable (PairEq (a, b) (c, d))

instance : DecidableEq Integer := inferInstanceAs <| DecidableEq (Quotient Setoid.NatPair)

@[reducible]
def Integer.from.nat : Nat -> Integer := fun n => Integer.mk (0, Natural.from.nat n)

instance (n: Nat) : OfNat Integer n where
  ofNat := Integer.from.nat n

def Integer.zero := Integer.mk (0, 0)

instance : Zero Integer := ⟨Integer.zero⟩

theorem Integer.mk_zero (a: Natural): Integer.mk (a, a) = 0 := by
  apply Quotient.sound
  change PairEq _ _
  unfold PairEq
  exact Natural.add_commutative a 0

theorem Integer.one (a: Natural): Integer.mk (a, a.successor) = 1 := by
  apply Quotient.sound
  change PairEq _ _
  unfold PairEq
  simp
  rw [successor.add, Natural.add_zero, Natural.add_commutative, Natural.add_one]

theorem Integer.left_right (i: Integer): ∃a: Natural, i = Integer.mk (0, a) ∨ i = Integer.mk (a, 0) := by
  cases i using Quotient.ind
  rename_i p
  let (a, b) := p
  cases Natural.le_total a b
  next h1 =>
    exists b -ₛ a
    left
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    rw [Natural.add_zero]
    exact (subtraction_eq_iff_eq_add h1).mp rfl
  next h1 =>
    exists a -ₛ b
    right
    apply Quotient.sound
    change PairEq _ _
    unfold PairEq
    simp
    rw [Natural.add_commutative]
    exact Natural.subtraction_lhs_addition''' a b h1

instance NatIntegerCoe : Coe Natural Integer := ⟨fun n => Integer.mk (0, n)⟩

def Integer.to_int (Integer: Integer): Int := Quotient.liftOn
  Integer
  (fun (a, b) => (Int.ofNat <| Natural.to.nat b) - (Int.ofNat <| Natural.to.nat a))
  (by
    intro (a, b) (c, d) h1
    change b + c = d + a at h1
    simp
    refine Int.sub_eq_iff_eq_add'.mpr ?_
    have h2: ∀a b c: Int, (a + (b - c)) = (a + b) - c := by exact fun a b c => Eq.symm (Int.add_sub_assoc a b c)
    rw [h2]
    symm
    refine Int.sub_eq_iff_eq_add'.mpr ?_
    have h3 : ∀a b: Natural, ((Natural.to.nat a + Natural.to.nat b): Int) = ↑(Natural.to.nat a + Natural.to.nat b) := fun _ _ => rfl
    have h4 : ∀a b: Natural, Natural.to.nat (a + b) = Natural.to.nat a + Natural.to.nat b := by
      intro a b
      induction a with
      | zero =>
        have : 0 = Natural.to.nat 0 := rfl
        rw [Natural.zero_def, Natural.zero_add, ←this, Nat.zero_add];
      | successor a ih =>
        have : ∀n: Natural, (Natural.to.nat n.successor) = (Natural.to.nat n).succ := fun _ => rfl
        rw [successor.add, this, ih, ←Nat.succ_add, ←this]
    rw [Int.add_comm, Int.add_comm (Natural.to.nat c), h3, h3, ←h4, ←h4, h1]
  )

instance (a b: NatPair) : Decidable (a ≈ b) :=
  inferInstanceAs (Decidable (a.snd + b.fst = b.snd + a.fst))
