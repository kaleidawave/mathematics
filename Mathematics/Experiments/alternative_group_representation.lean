structure GroupLike (T: Type) where
  bop : T → T → T
  inv : T → T
  id : T

section group

-- TODO local
variable { T: Type } { on: GroupLike T }

-- TODO can this be moved into the class definition?
set_option quotPrecheck false
infix:100 "⋆" => on.bop
local postfix:120 "⁻¹" => on.inv

class Group (id := on.id) where
associativity : ∀ a b c: T, a ⋆ (b ⋆ c) = (a ⋆ b) ⋆ c
identity : ∀ a: T, a ⋆ id = a ∧ id ⋆ a = a
inverse : ∀ a: T, (a⁻¹ ⋆ a) = id ∧ (a ⋆ a⁻¹) = id

end group

class Inv (T : Type) where
  inv : T → T

postfix:max "⁻¹" => Inv.inverse

def MulGroup (T: Type) [Mul T] [Inv T] [OfNat T 1]: Type := @Group T ⟨fun a b => a * b, fun a => a⁻¹, 1⟩ 1
def AddGroup (T: Type) [Add T] [Neg T] [OfNat T 0]: Type := @Group T ⟨fun a b => a + b, fun a => -a, 0⟩ 0
-- TODO ComposeGroup

namespace theorems

variable { T: Type } {on: GroupLike T} {g: @Group T on on.id} { a b c: T }

set_option quotPrecheck false
infix:100 "⋆" => on.bop
postfix:120 "⁻¹" => on.inverse

theorem left_identity : on.id ⋆ a = a := (g.identity a).2
theorem right_identity : a ⋆ on.id = a := (g.identity a).1

-- does't work :(
theorem inv_inv : (a⁻¹)⁻¹ = a := by
  rw [←left_identity (a⁻¹)⁻¹] -- ...

end theorems
