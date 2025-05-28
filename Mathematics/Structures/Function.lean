theorem identity_definition {T: Type} (x: T): id x = x := rfl

theorem composition_associative {T: Type} (a b c: T → T): (a ∘ b) ∘ c = a ∘ (b ∘ c) := rfl

theorem composition_identity {T: Type} (a: T → T): id ∘ a = a := rfl

theorem composition_definition {T U V: Type} (a: U → V) (b: T → U) (x: T): (a ∘ b) x = a (b x) := rfl
