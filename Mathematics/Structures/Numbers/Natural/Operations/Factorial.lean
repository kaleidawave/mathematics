import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Multiplication
import Mathematics.Structures.Numbers.Natural.Divides
import Mathematics.Structures.Numbers.Natural.Inequality

/-- TODO class and syntax? -/
def factorial : Natural → Natural
| 0 => 1
| a@(.successor b) => a * (factorial b)

#eval factorial 3

theorem factorial.zero : factorial 0 = 1 := rfl
theorem factorial.successor (n: Natural) : factorial (n.successor) = n.successor * factorial n := rfl

theorem factorial.divides_self (n: NonZeroNatural) : ↑n ∣ factorial n := by
  match n with
  | ⟨1, _⟩ => exact ⟨1, rfl⟩
  | ⟨.successor n, _⟩ => {
    rw [factorial.successor, multiply.commutative];
    exists factorial n
  }

open divides

theorem less_than_divides (n: NonZeroNatural) (N: Natural) (h1: n <= N) : ↑n ∣ (factorial N) := by
  obtain ⟨m, h1⟩ := h1
  rw [←h1]
  clear h1
  have d := n.property
  sorry
