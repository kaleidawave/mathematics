import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Natural.Addition

inductive Sign : Type | positive | negative deriving BEq

theorem Sign.binary_relation (p1 p2: Sign): p1 == p2 ∨ p1 != p2 := by
  match p1, p2 with
  | Sign.positive, Sign.positive => left; rfl
  | Sign.negative, Sign.negative => left; rfl
  | Sign.positive, Sign.negative => right; rfl
  | Sign.negative, Sign.positive => right; rfl

theorem Sign.neq {p1 p2: Sign} (h1: p1 != p2): ¬(p1 == p2) := by
  match p1, p2 with
  | Sign.positive, Sign.positive => contradiction
  | Sign.negative, Sign.negative => contradiction
  | Sign.positive, Sign.negative => simp; rfl
  | Sign.negative, Sign.positive => simp; rfl

instance : PartialEquivBEq Sign where
  symm := by
    intro p1 p2 h1;
    cases p1
    cases p2; rfl; contradiction
    cases p2; contradiction; rfl;
  trans := by
    intro p1 p2 p3 h1 h2;
    cases p1;
    cases p2; exact h2; contradiction;
    cases p2; contradiction; exact h2;

theorem Sign.neq_comm {p1 p2: Sign}: (p1 != p2) = (p2 != p1) := bne_comm
theorem Sign.comm {p1 p2: Sign}: (p1 == p2) = (p2 == p1) := BEq.comm

theorem Sign.ne: Sign.positive ≠ Sign.negative := by intro h1; contradiction;

open Natural in
def Integer.sign (Integer: Integer): Sign := Quotient.liftOn
  Integer
  (fun (a, b) => if a <= b then Sign.positive else Sign.negative)
  (by
    intro (a, b) (c, d) pair_eq
    change PairEq (a, b) (c, d) at pair_eq
    unfold PairEq at pair_eq
    simp at pair_eq |-

    cases Natural.lt_trichotomy a b with
    | inl h1 => {
      have h3 : a <= b := Natural.less_than_implies_less_than_equal h1
      obtain ⟨l, h1⟩ := h3
      rw [←h1, add_commutative d, add_associative, add_left_cancel, add_commutative] at pair_eq
      rw [if_pos ⟨l, h1⟩, if_pos ⟨l, pair_eq⟩]
    }
    | inr h1 => cases h1 with
    | inl h1 => {
      rw [h1] at |- pair_eq
      rw [add_commutative d, add_left_cancel] at pair_eq
      have b_lt: b <= b := Natural.less_than.equal.self _
      have c_lt: c <= d := pair_eq ▸ (Natural.less_than.equal.self _)
      rw [if_pos b_lt, if_pos c_lt]
    }
    | inr h1 => {
      have ⟨l, bd⟩ := h1
      rw [
        ←bd,
        successor.add, ←add.successor,
        ←add_associative, add_commutative _ b, add_associative, add_left_cancel,
        add.successor, ←successor.add
      ] at pair_eq
      have h2: c > d := ⟨l, pair_eq.symm⟩
      have h1: ¬(a <= b) := Natural.less_than_not_greater_than.mp h1
      have h2: ¬(c <= d) := Natural.less_than_not_greater_than.mp h2
      rw [if_neg h1, if_neg h2]
    }
  )
