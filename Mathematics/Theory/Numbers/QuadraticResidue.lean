import Mathematics.Theory.Numbers.Coprime
import Mathematics.Theory.Numbers.ModuloCongruence

-- Order
-- and exists b such a = b ^ 2 mod n

def is_quadratic_modulo (a m: Natural): Prop := is_coprime a m ∧ ∃b: Natural, a ≡ b * b mod m
