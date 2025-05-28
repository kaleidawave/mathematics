class Field (T: Type) extends Zero T, OfNat T 1, Add T, Sub T, Neg T, Mul T, Div T, LE T, LT T where
different: (0: T) ≠ (1: T)
add_zero: ∀x: T, x + 0 = x
zero_add: ∀x: T, 0 + x = x
add_associative: ∀a b c: T, a + (b + c) = (a + b) + c
add_commutative: ∀a b: T, a + b = b + a
zero_mul: ∀x: T, 0 * x = 0
one_mul: ∀x: T, 1 * x = x
mul_associative: ∀a b c: T, a * (b * c) = a * b * c
mul_commutative: ∀a b: T, a * b = b * a
neg_def: ∀x: T, -x = -1 * x
sub_eq: ∀x y: T, x = y ↔ x - y = 0
sub_def: ∀x y: T, x - y = x + (-1 * y)
distributive: ∀a b c: T, a * c + b * c = (a + b) * c
-- TODO can this one be proven from above?
neg_neg: ∀x: T, - (-x) = x
div_self : ∀a: T, (a / a) = 1
add_neg_assoc : ∀a b c: T, a - (b + c) = a - b - c
add_neg_rerrange : ∀a b c d: T, a + b - c - d = (a - c) + (b - d)
-- Double check
add_neg_rerrange₂ : ∀a b c d: T, a - b + (c - d) = (a - d) - (b - c)
-- TODO can these be proven
div_add: ∀a b c: T, (a / c) + (b / c) = (a + b) / c
div_mul: ∀a b c: T, (a * b) / c = a * (b / c)

theorem Field.sub_distributive {T: Type} [Field T] (a b c: T): a * b - a * c = a * (b - c) := by
  rw [
    sub_def,
    mul_commutative a c,
    mul_associative,
    mul_commutative a _,
    distributive,
    ←sub_def,
    mul_commutative a _,
  ]

theorem Field.distributive' {T: Type} [f: Field T] (a b c: T): a * b + a * c = a * (b + c) := by
  rw [f.mul_commutative a (b + c), ←f.distributive, f.mul_commutative a b, f.mul_commutative c a]

-- TODO via calc
theorem Field.difference_of_squares {T: Type} [Field T] (a b: T) : (a * a - b * b) = (a + b) * (a - b) := by
  rw [
    ←distributive,
    ←sub_distributive,
    ←sub_distributive,
    add_neg_rerrange₂,
    -- This line is a little complex
    (sub_eq (a * b) (b * a)).mp (mul_commutative a b),
    -- TODO this can be extracted as their own theorems
    sub_def _ 0,
    mul_commutative _ 0,
    zero_mul,
    add_zero
  ]

theorem Field.sub_zero {T: Type} [Field T] (a: T) : a - 0 = a := by
  rw [Field.sub_def, Field.mul_commutative, Field.zero_mul, Field.add_zero]

theorem Field.mul_one {T: Type} [Field T] (a: T) : a * 1 = a := (Field.mul_commutative _ (1: T)) ▸ Field.one_mul a

theorem Field.add_self {T: Type} [Field T] (a: T): a + a = (1 + 1) * a := by
  conv => lhs; rw [←Field.one_mul a];
  rw [Field.distributive]

class OrderedField (T: Type) [Field T] extends LE T, LT T where
eq_then_leq: ∀a: T, a = a → a <= a
total: ∀a b: T, a < b ∨ a >= b
le_def: ∀a b: T, a <= b ↔ (a = b ∨ a < b)
gt_zero_one: 0 < (1: T)
-- TODO this might need some work
le_def₂: ∀a b: T, a <= b ↔ ∃c: T, c >= 0 ∧ a + c = b

lt_lt_trans : ∀a b c: T, a < b → b < c → a < c
ge_one_two: 1 <= (1 + 1: T)
gt_zero_two: 0 < (1 + 1: T)
gt_one_two: 1 < (1 + 1: T)
lt_div : ∀a b: T, a > b → (a / (1 + 1)) > b
lt_add: ∀a b c d: T, a < b → c < d → (a + c) < (b + d)
lt_sub: ∀a b c: T, a - b > c → a > b + c
lt_sub': ∀a b c: T, a - b < c → a < c + b
lt_mul_cancel: ∀a b c: T, b > 0 → b * a < b * c → a < c

theorem OrderedField.lt_implies_le {T: Type} [Field T] [OrderedField T] (a b: T) (h1: a < b) : a <= b := (OrderedField.le_def a b).mpr (Or.inr h1)

theorem OrderedField.le_lt_trans {T: Type} [Field T] [OrderedField T] (a b c: T) (h1: a <= b) (h2: b < c): a < c := by
  cases (OrderedField.le_def a b).mp h1 with
  | inl h3 => rw [h3]; exact h2
  | inr h3 => exact OrderedField.lt_lt_trans a b c h3 h2

theorem OrderedField.lt_le_trans {T: Type} [Field T] [OrderedField T] (a b c: T) (h1: a < b) (h2: b <= c): a < c := by
  cases (OrderedField.le_def b c).mp h2 with
  | inl h3 => rw [←h3]; exact h1
  | inr h3 => exact OrderedField.lt_lt_trans a b c h1 h3

theorem OrderedField.ge_zero_one {T: Type} [Field T] [OrderedField T] : 0 <= (1: T) := (OrderedField.le_def 0 1).mpr (Or.inr OrderedField.gt_zero_one)

theorem OrderedField.ge_zero_two {T: Type} [Field T] [OrderedField T] : 0 <= (1 + 1: T) := by
  sorry
  -- rw [OrderedField.le_def₂]
  -- exists (1 + 1)

def Real: Type := sorry

-- variable {Real: Type} [Field Real] [OrderedField Real]
-- variable [Field Real] [OrderedField Real]

instance : Field Real := sorry
instance : OrderedField Real := sorry

-- TODO constraints
class FieldWithAbsConjugate (T: Type) extends Field T where
  abs: T → Real
  conigate: T → T

example : (0: Real) ≠ (1: Real) := Field.different

-- class ConjugateField (T: Type) extends Field T
-- conjugate: T → T
