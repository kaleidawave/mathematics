import Mathematics.Algebra.Field

class Abs {F: Type} [Field F] [OrderedField F] (abs: F → Real) where
positive: ∀a: F, abs a >= 0
equal: ∀a: F, abs a = 0 ↔ a = 0
multiplicative: ∀a b: F, abs (a * b) = (abs a) * (abs b)
negative: ∀a: F, abs (-a) = abs a
