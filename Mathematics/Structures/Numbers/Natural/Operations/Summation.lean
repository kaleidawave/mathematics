import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Subtraction
import Mathematics.Structures.Numbers.Natural.Inequality

def Natural.sum {T: Type} [Add T] [Zero T] (f: Natural → T): Natural → T
| .zero => 0
| n@(.successor ns) => (Natural.sum f) ns + f n

-- def Natural.sumInclusive {T: Type} [Add T] (f: Natural → T): Natural → T
-- | n@.zero => f n
-- | n@(.successor ns) => (Natural.sum f) ns + f n

theorem Sum.zero {T: Type} [Add T] [Zero T] (f: Natural → T): (Natural.sum f 0) = 0 := rfl
theorem Sum.zerod {T: Type} [Add T] [Zero T] (f: Natural → T): (Natural.sum f Natural.zero) = 0 := rfl

theorem Sum.successor {T: Type} [Add T] [Zero T] (f: Natural → T) (n: Natural): (Natural.sum f n.successor) = (Natural.sum f n) + f n.successor := rfl

def Natural.sum.between {T: Type} [Add T] [Zero T] (f: Natural → T) (from' to: Natural): T := if
  from' <= to
  then
    (to -ₛ from').sum (fun n => f (n + from'))
  else
    0

-- theorem Natural.sum.between.zero {T: Type} [Add T] [Zero T] (f: Natural → T) (from' to: Natural):
--   Natural.sum.between f from' 0 = Natural.sum.between f from' to + f to.successor
-- := by
--   induction to with
--   | zero => sorry
--   | successor to ih => sorry

theorem Natural.sum.between.successor {T: Type} [Add T] [Zero T] (f: Natural → T) (from' to: Natural):
  Natural.sum.between f from' to.successor = Natural.sum.between f from' to + f to.successor
:= by
  induction from' with
  | zero => {
    unfold between;
    rw [if_pos, if_pos, subtraction.rhs.zerod, subtraction.rhs.zerod, Sum.successor, Natural.add.zerod];
    exact Natural.greater_than.equal.zero to;
    exact Natural.greater_than.equal.zero to.successor;
  }
  | successor from' ih => {
    unfold between;
    sorry
    -- rw []

    -- rw [ih]
  }

-- theorem Natural.sum.pop (f: Natural → Natural) (n: Natural):
--   Natural.sum f n = f 0 + Natural.sum.between f 1 n
-- := by
--   induction n with
--   | zero => {
--     unfold between
--     -- TODO needs to be group
--     rw [if_neg, Natural.add.zero]
--     rfl
--     exact of_decide_eq_false rfl
--   }
--   | successor n ih => {
--     unfold between at |- ih
--     -- rw [Sum.successor, ih]
--     rw [if_pos, ←successor.zero_eq_one, subtraction.successor, subtraction.rhs.zero]
--     rw [Sum.successor]
--     sorry
--     sorry
--   }

section theorems

-- TODO ring
theorem sum_distributive (n: Natural) (f: Natural → Natural) (c: Natural): n.sum (fun i => c * f i) = c * n.sum f := by
  induction n with
  | zero => rw [Sum.zerod, Sum.zerod, multiply.zero];
  | successor n ih => {
    rw [Sum.successor, ih, ←multiply.distributive, ←Sum.successor]
  }

theorem sum_of_add (n: Natural) (f g: Natural → Natural): n.sum (fun i => f i + g i) = n.sum f + n.sum g := by
  induction n with
  | zero => rfl
  | successor n ih => {
    rw [Sum.successor, ih]
    rw [
      ←add.associative,
      add.associative (Natural.sum f n),
      add.commutative _ (f n.successor),
      ←add.associative,
      add.associative _ _ (g n.successor),
    ]
    rw [←Sum.successor, ←Sum.successor]
  }

end theorems

section examples

theorem sum_constant (n c: Natural): n.sum (fun _ => c) = c * n := by
  induction n with
  | zero => rw [Sum.zerod, multiply.zerod];
  | successor n ih => rw [Sum.successor, ih, ←multiply.successor]

theorem sum_sequence (n: Natural): 2 * n.sum id = n * (n + 1) := by
  induction n with
  | zero => rfl
  | successor n ih => {
    have id_app: ∀x: Natural, id x = x := fun x => rfl
    -- TODO tidy
    rw [
      Sum.successor,
      multiply.distributive,
      ih,
      successor.multiply,
      add.one,
      add.one,
      multiply.successor,
      multiply.successor,
      multiply.successor,
      multiply.commutative 2,
      id_app,
      multiply.two,
      successor.add,
      ←add.successor,
      add.associative,
      add.associative,
      add.associative
    ]
  }

end examples
