import Mathematics.Algebra.Group
import Mathematics.Algebra.Monoid
import Mathematics.Structures.Numbers.Natural

class Ring (T: Type) extends AbelianGroup T, Monoid T, Mul T, Add T, OfNat T 1, OfNat T 0 :=
distributive: ∀a b c: T, a * (b + c) = a * b + a * c ∧ (b + c) * a = b * a + c * a

def Ring.power {T: Type} [Ring T] (a: T) (n: Natural) : T := match n with
| Natural.zero => 1
| Natural.successor n => (Ring.power a n) * a

-- TODO show this a ring
def Ideal (T: Type) [Ring T] (g: T) : Type := { t: T // ∃n: Natural, t = Ring.power g n }
