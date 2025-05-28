import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Power
import Mathematics.Theory.Numbers.Prime

-- TODO move and maybe requires integers
theorem EuclidDivision (a b: Natural) (h1: b ≠ 0): ∃q r: Natural, a = q * b + r ∧ r < b := by
  induction a generalizing b with
  | zero =>
    exists 0
    exists 0
    rw [zero.multiply, zero.add]
    exact ⟨rfl, Natural.less_than.neq_zero b h1⟩
  | successor a ih =>
    have e : b.successor ≠ 0 :=  successor.neq.zero b
    have d := ih b.successor e
    obtain ⟨q, ih⟩ := d
    obtain ⟨r, ⟨iha, ihb⟩⟩ := ih
    exists q
    exists (q + r).successor
    constructor
    {
      rw [multiply.successor, add.associative] at iha
      rw [add.successor, successor.pure]
      exact iha
    }
    {
      obtain ⟨d, h1⟩ := ihb
      exists d

      -- rw [succ]
      sorry
    }

-- inductive Counted (T: Type): Type
-- | empty: Counted T
-- | succ (n: Natural) (item: T) (tail: Counted T): Counted T

def PrimeDivisors: Type := List Prime

def PrimeDivisors.from : PrimeDivisors → Natural
| List.nil => 1
| List.cons n head => n.val * PrimeDivisors.from head

theorem FundamentalTheoremOfArithmentic : ∀a: Natural, ∃divs: PrimeDivisors, divs.from = a := sorry
