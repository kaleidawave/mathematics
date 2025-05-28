class PartialOrder (T: Type) (relation: T → T → Prop) where
reflexivity: ∀a: T, relation a a
antisymmetric: ∀a b: T, (relation a b) ∧ (relation b a) → a = b
transitivity: ∀a b c: T, (relation a b) ∧ (relation b c) → (relation a c)

class StrictPartialOrder (T: Type) (relation: T → T → Prop) where
irreflexivity: ∀a: T, ¬relation a a
asymmetric: ∀a b: T, (relation a b) → ¬(relation b a)
transitivity: ∀a b c: T, (relation a b) ∧ (relation b c) → (relation a c)

class TotalOrdering (T: Type) (relation: T → T → Prop) extends PartialOrder T relation where
strongly_connected: ∀a b: T, (relation a b) ∨ relation b a

class StrictTotalOrdering (T: Type) (relation: T → T → Prop) extends StrictPartialOrder T relation where
strongly_connected: ∀a b: T, a ≠ b → (relation a b) ∨ relation b a
