import Mathematics.Algebra.Ring

class Field (T: Type) extends Ring T, Mul T, Add T, OfNat T 1, OfNat T 0 :=
non_equiv: (1: T) ≠ (0: T)

-- TODO I think
def Field.extension (T U: Type) (u: U) [Field T] [HAdd T U U] [HMul T U U]: Type := { t: U // ∃a b: T, t = a + b * u }

#eval 2
