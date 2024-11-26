class PartialOrder (T: Type) (relation: T → T → Prop) :=
reflexivity : ∀ a: T, relation a a
antisymmetric : ∀ a b: T, (relation a b) ∧ (relation b a) → a = b
transitivity : ∀ a b c: T, (relation a b) ∧ (relation b c) → (relation a c)
