import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Addition
import Mathematics.Structures.Numbers.Natural.SaturatingSubtraction

unsafe def Natural.divide (a b: Natural): Option Natural :=
 if b = 0 then none
 else if a < b then some 0
 else .successor <$> (Natural.divide (a -ˢ b) b)

infix:60 " / " => Natural.divide

#eval (10: Natural) / (2 : Natural)

unsafe example (a: Natural) : a / (1: Natural) = a := by
  induction a with
  | zero => {
    have x : Natural.zero < 1 := ⟨0, by rw [Natural.add.zero, successor.zero_eq_one]⟩
    sorry
  }
  | successor n ih => {
    sorry
  }
