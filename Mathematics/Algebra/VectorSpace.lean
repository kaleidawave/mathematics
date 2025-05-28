import Mathematics.Algebra.Field

class VectorSpace (X F: Type) [Field F] extends Zero X, OfNat X 1, Add X, Sub X, HMul F X X, Neg X where
zero_mul: ∀x: X, (0: F) * x = (0: X)
one_mul: ∀x: X, (1: F) * x = x
add_zero: ∀x: X, x + (0: X) = x
sub_eq: ∀x y: X, x = y ↔ x - y = 0
sub_def: ∀x y: X, x - y = x + ((-1: F) * y)
neg_def: ∀x: X, -x = (-1: F) * x
mul_associative: ∀x: X, ∀a b: F, a * (b * x) = (a * b) * x
add_commutative: ∀x y: X, x + y = y + x
distributive: ∀b c: X, ∀a: F, a * b + a * c = a * (b + c)

instance {T: Type} [f: Field T] : VectorSpace T T where
zero_mul := f.zero_mul
one_mul := f.one_mul
add_zero := f.add_zero
sub_eq := f.sub_eq
sub_def := f.sub_def
neg_def := f.neg_def
add_commutative := f.add_commutative
mul_associative := fun a b c => f.mul_associative b c a
distributive := fun a b c => f.distributive' c a b
