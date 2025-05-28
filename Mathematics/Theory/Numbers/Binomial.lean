import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Inequality
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.Operations.Summation
import Mathematics.Structures.Numbers.Natural.Operations.Factorial
import Mathematics.Structures.Numbers.Natural.Subtraction
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Power

  -- if k > 0
  -- then 0
  -- else
def BinomialCoefficient (n k: Natural): Natural :=
  match n, k with
  | _, Natural.zero => 1
  | .successor ns, .successor nk => (BinomialCoefficient ns nk) + BinomialCoefficient ns k
  | .zero, .successor _ => 0

notation (name := binomial_coefficient) "⸨" n: 50 ", " m:50 "⸩" => BinomialCoefficient n m

theorem BinomialCoefficient.zero (n: Natural): ⸨n, 0⸩ = 1 := by cases n <;> rfl

theorem BinomialCoefficient.gt (n k: Natural) (h1: n < k): ⸨n, k⸩ = 0 := by
  have ⟨c, h2⟩ := h1
  cases k with
  | zero => rw [successor.add] at h2; exact successor.neq.zero _ h2 |>.elim
  | successor k => {
    clear h1
    induction n generalizing c with
    | zero => rfl
    | successor n ih => {
      have h3 := h2
      rw [successor.add, ←add.successor] at h2
      specialize ih c.successor h2
      rw [BinomialCoefficient.eq_2, ih, Natural.add.zero]
      rw [successor.add, ←successor.iff] at h3
      have h1: n < k := ⟨c, h3⟩
      exact BinomialCoefficient.gt _ _ h1
    }
  }

-- #eval ⸨0, 1⸩

theorem BinomialCoefficient.self (n: Natural): ⸨n, n⸩ = 1 := by
  induction n with
  | zero => rfl
  | successor n ih => {
    rw [BinomialCoefficient.eq_2, ih]
    have h1 : n < n.successor := ⟨0, Natural.add.zero n.successor⟩
    have h2 : ⸨n, n.successor⸩ = 0 := BinomialCoefficient.gt _ _ h1
    rw [h2]
    rfl
  }

theorem BinomialCoefficient.fact2 (n k: Natural): ⸨n + k, k⸩ = 1 := by
  sorry

theorem BinomialCoefficient.fact (n k: Natural) (h1: n >= k):
  ⸨n, k⸩ * (factorial k) * factorial (n -ₛ k) = factorial n
:= by
  obtain ⟨c, h1⟩ := h1
  rw [←h1]
  clear h1
  induction k with
  | zero => {
    rw [Natural.zero_def, BinomialCoefficient.zero, factorial.zero, subtraction.rhs.zero, multiply.one, one.multiply]
  }
  | successor k ih => {
    rw [subtraction.lhs.addition'] at ih
    rw [
      successor.add,
      BinomialCoefficient.eq_2,
      factorial.successor,
      factorial.successor,
      subtraction.successor,
      subtraction.lhs.addition',
      ←ih,
    ]
    sorry
  }

-- #eval BinomialCoefficient 4 2

-- def row: Natural := 7
-- #eval (List.range (Natural.to.nat row).succ).map Natural.from.nat |>.map (fun x => ⸨row, x⸩)

-- variable (x: Natural)

def BinomialExpansion (x y n: Natural): Natural := Natural.sum (fun k => (⸨n, k⸩) * (x ^ (n -ₛ k)) * (y ^ k)) n

-- theorem BinomialTheorem₁ (x n: Natural): (1 + x) ^ n = BinomialExpansion 1 x n := by
--   induction n with
--   | zero => {
--     rw [Natural.zero_def, power.zero]
--     unfold BinomialExpansion
--     suffices ⸨0, 0⸩ * (x ^ (0: Natural)) * 1 ^ 0 -ₛ 0 = 1 by rfl
--     rw [
--       subtraction.self,
--       BinomialCoefficient.zero,
--       power.zero,
--       power.zero,
--       multiply.one,
--       multiply.one
--     ]
--   }
--   | successor n ih => {
--     rw [power.successor, ih]
--     unfold BinomialExpansion at |-
--     rw [
--       Sum.successor,
--       one.power,
--       subtraction.self,
--       power.zero,
--       multiply.one,
--       multiply.one,
--     ]
--     -- rw [
--     --   one.power,
--     -- ]
--     -- https://proofwiki.org/wiki/Binomial_Theorem/Integral_Index
--     sorry
--     -- let prev := Natural.sum (fun k => BinomialCoefficient n k * x ^ k * y ^ n -ₛ k) n
--     -- rw [Sum.successor, ←ih]
--   }

-- def Natural.sum_to {T: Type} [Add T] [Zero T] (f: Natural → T) (start to: Natural): T :=
--   if start > to
--     then 0
--     else
--       match start with
--       | n@.zero => f n
--       | n@(.successor ns) => (Natural.sum_to f start) ns + f n

theorem BinomialTheorem₂ (x y n: Natural): (x + y) ^ n = BinomialExpansion x y n := by
  induction n with
  | zero => {
    rw [Natural.zero_def, power.zero]
    unfold BinomialExpansion
    suffices BinomialCoefficient (0: Natural) 0 * (x ^ (0: Natural)) * y ^ 0 -ₛ 0 = 1 by sorry
    rw [subtraction.self, BinomialCoefficient.zero, power.zero, power.zero, multiply.one, multiply.one]
  }
  | successor n ih => {
    unfold BinomialExpansion at |- ih
    -- let prev := Natural.sum (fun k => BinomialCoefficient n k * x ^ k * y ^ n -ₛ k) n
    rw [
      power.successor,
      ih,
      multiply.distributive,
      multiply.commutative _ x,
      multiply.commutative _ y,
      sum_distributive,
      sum_distributive
    ]
    conv => lhs; lhs; arg 1; intro k; rw [
      ←multiply.associative x,
      ←multiply.associative x,
      multiply.commutative,
      multiply.associative,
      multiply.commutative x,
      multiply.associative,
      ←power.successor,
    ]


    -- TODO merge to get x^k.successor. separate out first term. rewrite via reverse one identities. and merge back
    sorry

    -- suffices (x + y) ^ n.successor = prev + BinomialCoefficient n (n.successor) * x ^ (n.successor) * y ^ n -ₛ (n.successor) by rfl

    -- rw [power.successor]
  }

/-



-- #eval Natural.sum (fun n => 1) 2
-/
