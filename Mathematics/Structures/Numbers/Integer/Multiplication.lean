import Mathematics.Structures.Numbers.Integer
import Mathematics.Structures.Numbers.Integer.Subtraction

def Integer.multiply : Integer → Integer → Integer
  | ⟨(a, 0), _⟩, ⟨(b, 0), _⟩ => ⟨⟨a * b, 0⟩, by exact Or.inr rfl⟩
  | ⟨(0, a), _⟩, ⟨(0, b), _⟩ => ⟨⟨a * b, 0⟩, by exact Or.inr rfl⟩
  | ⟨(0, a), _⟩, ⟨(b, 0), _⟩ => ⟨⟨0, a * b⟩, by exact Or.inl rfl⟩
  | ⟨(a, 0), _⟩, ⟨(0, b), _⟩ => ⟨⟨0, a * b⟩, by exact Or.inl rfl⟩
  | ⟨(.successor a, .successor b), p⟩, _ => by simp at p;
  | _, ⟨(.successor a, .successor b), p⟩ => by simp at p;

instance : Mul Integer := { mul := Integer.multiply }

#eval (62: Integer) * -7
