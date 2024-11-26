class Relation (T: Type) (relation: T → T → Prop) :=
reflexivity : ∀ a: T, relation a a
symmetric : ∀ a b: T, (relation a b) → (relation b a)
transitivity : ∀ a b c: T, (relation a b) ∧ (relation b c) → (relation a c)

def Pair (T: Type) := Prod T T

-- TODO I don't think this is the correct definition
def ConjugacyClass (T: Type) (relation: (Pair T) → (Pair T) → Prop) [Relation (Pair T) relation] := Pair T

-- TODO is this even possible
-- instance (T: Type) (relation: (Pair T) → (Pair T) → Prop) [Relation (Pair T) relation]: Eq (ConjugacyClass T relation) (ConjugacyClass T relation) := sorry -- (ConjugacyClass T relation)
