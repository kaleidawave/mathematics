import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Inequality

def Natural.min.of (n m: Natural) : Natural := if n <= m then n else m

-- Similar to Exists
-- TODO https://leanprover-commutativeunity.github.io/mathlib4.docs/Mathlib/Init/Data/Nat/Lemmas.html#Nat.find
def Natural.min.under (n: Natural) (p: Natural → Prop) : Prop := p n ∧ ¬∃m: Natural, m <= n → p m

def Natural.max.of (n m: Natural) : Natural := if n <= m then m else n

example : min 2 4 = 2 := by unfold min; rfl
