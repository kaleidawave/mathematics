import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Modulo

def gcd (m n : Natural) : Natural :=
  if m = 0 then
    n
  else
    gcd (n % m) m
  decreasing_by {

  }

-- #eval Natural.modulo 15 6
-- #eval (5: Natural) % 10
-- #eval (10: Natural) % 5
-- #eval! gcd 10 5
-- #eval! gcd 5 10

-- def gcd2 (m n : Nat) : IO Nat := do
--   IO.println s!"gcd {m} {n}"
--   if m = 0 then
--     pure n
--   else
--     gcd2 (n % m) m
--   -- termination_by m
--   -- decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption

-- #eval 5 % 10
-- #eval 10 % 5
-- #eval! gcd2 10 5
