class Relation (T: Type) (relation: T → T → Prop) :=
reflexivity : ∀ a: T, relation a a
symmetric : ∀ a b: T, (relation a b) → (relation b a)
transitivity : ∀ a b c: T, (relation a b) ∧ (relation b c) → (relation a c)