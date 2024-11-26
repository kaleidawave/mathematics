import Mathematics.Structures.Numbers.Natural

def is_fixed_point { T: Type } (x: T) (f: T → T) : Prop := f x = x

def repeated_apply { T: Type } (f: T → T) (n: Natural) (a: T) : T := match n with
-- TODO contraversal
| Natural.zero => a
| Natural.successor n => repeated_apply f n (f a)

/- adding three four times to 2 results in 14 -/
example : repeated_apply (. + 3) 4 2 = 14 := rfl

def function.point_free { T: Type } (f: T → T) : Prop := ∀t: T, f t ≠ t

def function.is_involution { T: Type } (f: T → T) : Prop := ∀t: T, f (f t) = t
