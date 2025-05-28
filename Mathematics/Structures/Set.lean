import Mathematics.Logic

def Set (A: Type): Type := A → Prop

@[simp]
theorem Set.extensionality (s₁ s₂: Set A) : s₁ = s₂ ↔ ∀ a: A, s₁ a ↔ s₂ a := by
  constructor
  {
   intro h1 a
   rw [h1]
  }
  {
    intro h1
    funext a
    exact propext (h1 a)
  }

@[ext]
theorem Set.extensionality₂ (s₁ s₂: Set A) (h1: ∀ a: A, s₁ a ↔ s₂ a ) : s₁ = s₂ := (Set.extensionality s₁ s₂).mpr h1

/-- Containing all items of a type -/
@[simp]
def Set.universal (A: Type) : Set A := fun _ => True

/-- Containing a single item -/
@[simp]
def Set.singleton {A: Type} (a: A) : Set A := fun item => item = a

/-- A set with no items -/
@[simp]
def Set.empty (A: Type) : Set A := fun _ => False

notation "∅" => Set.empty _

@[simp, reducible]
def Set.includes (z: Set A) (a: A) : Prop := z a

@[simp, reducible]
instance { A: Type }: Membership A (Set A) := ⟨fun z a => z a⟩

-- syntax (name := emptyset) "s{}" : term
-- syntax (name := set) "s{" term,+ "}" : term

-- macro_rules (kind := emptyset) | `(s{}) => `(Set.empty)

-- macro_rules (kind := set)
--   | `(s{ $x }) => `(Set.singleton $x)
--   | `(s{ $x, $xs,* }) => `(operators.Set.union (Set.singleton $x) (s{ $[$xs: term],* }))
