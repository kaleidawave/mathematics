import Mathematics.Algebra.Group
import Mathematics.Relation.Relation

def conjugation { T: Type } [Group T] (c: T) := fun (x: T) => c * x * c⁻¹

variable {T: Type} [Group T]

def are_conjugate (x x': T) : Prop := ∃g, x' = conjugation g x

open groups in
instance : Relation T are_conjugate := {
  symmetric := by
    intro a b h1
    let ⟨g, h2⟩ := h1
    exists g⁻¹
    unfold conjugation at *
    rw [
      h2,
      inv.double,
      multiply.associative,
      ←multiply.associative _ g⁻¹ g,
      (Group.inverse g).1,
      multiply.one,
      multiply.associative,
      (Group.inverse g).1,
      one.multiply
    ]
  reflexivity := by
    intro a
    exists 1
    unfold conjugation at *
    rw [one.multiply, one.inverse, multiply.one]
  transitivity := by
    intro a b c h1
    let ⟨⟨g1, h2⟩, ⟨g2, h3⟩⟩ := h1
    exists (g2 * g1)
    unfold conjugation at *
    rw [h3, h2, inv.multiply, multiply.associative, multiply.associative, multiply.associative]
}
