import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Divides
import Mathematics.Structures.Numbers.Natural.Inequality

/-- TODO class and syntax? -/
def Natural.factorial : Natural → Natural
| 0 => 1
-- TODO ISSUE: can bind and reuse?
| (.successor a) => (.successor a) * (factorial a)

-- TODO ISSUE: #eval (3: Natural).factorial Doesn't work :?
#eval Natural.factorial 3
-- #eval (Natural.factorial 0, Natural.factorial 1, Natural.factorial 2, Natural.factorial 3)

theorem factorial.successor (n: Natural) : Natural.factorial (n.successor) = n.successor * Natural.factorial n := rfl

theorem factorial.divides_self (n: NonZeroNatural) : ↑n ∣ Natural.factorial n := by
  match n with
  | ⟨1, _⟩ => exact ⟨1, rfl⟩
  | ⟨.successor n, _⟩ => {
    rw [factorial.successor, multiply.commutative];
    exact divides.multiple _ _
  }

open divides

theorem less_than_divides (n: NonZeroNatural) (N: Natural) (h1: n <= N) : ↑n ∣ (Natural.factorial N) := by
  induction N with
  | zero => sorry
  | successor n2 ih => {
    rw [factorial.successor]
    -- let ⟨a, b⟩ := h1
    have h2 : n.val ≤ n2 := by sorry
    have ⟨b, h3⟩ := ih h2
    exact ⟨b * n2.successor, by {
      rw [←h3, multiply.commutative b _, multiply.associative]
    }⟩
  }

-- TODO chose function etc
