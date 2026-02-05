import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations

syntax (name := emptyset) "s{}" : term
syntax (name := set) "s{" term,+ "}" : term

macro_rules (kind := emptyset) | `(s{}) => `(Set.empty)

macro_rules (kind := set)
  | `(s{ $x }) => `(Set.singleton $x)
  | `(s{ $x, $xs,* }) => `(Set.union (Set.singleton $x) (s{ $[$xs: term],* }))

-- def first_three: Set Nat := s{1, 2, 3}
