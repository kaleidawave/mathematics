import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Subtraction

@[reducible]
def Integer.less_than : Integer → Integer → Prop := fun a b => (b - a - 1).is_positive

instance : LT Integer where
  lt := Integer.less_than

instance (a b : Integer) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Integer.less_than a b))

#eval Integer.less_than 51 52
#eval Integer.less_than 52 52
#eval Integer.less_than 53 52
#eval Integer.less_than (-2) (-1)

#eval (62: Integer) < 63
