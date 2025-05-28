import Mathematics.Structures.Numbers.Natural
import Mathematics.Structures.Numbers.Natural.Divides
import Mathematics.Theory.Numbers.Prime

def is_coprime (n m: Natural): Prop := ∀a: Natural, (a ∣ n ∧ a ∣ m) → a = 1

-- gcd = 1

theorem tt : is_coprime 2 3 := by
  intro a ⟨l, r⟩
  have alt : a <= 2 :=  divides.less_than a 2 l (Ne.symm (ne_of_beq_false rfl))
  have tnd2 : ¬(2 ∣ 3) := by
    intro ⟨a, h1⟩
    sorry --even mul

  induction a with
  | zero => {
    sorry
    -- have
  }
  | successor a ih => {
    obtain ⟨c, l⟩ := l
    obtain ⟨d, r⟩ := r
    rw [multiply.successor] at l
    rw [multiply.successor] at r
    sorry
  }

theorem coprime_one (n: Natural): is_coprime 1 n := by
  intro a ⟨l, _⟩
  exact (divides.one a).mp l

-- TODO replace with gcd symmetric
theorem coprime.symmetric (n m: Natural): is_coprime m n → is_coprime n m := by
  intro coprime a h2
  exact (coprime a) (And.symm h2)

theorem coprime.primes (p q: Prime) (h1: p ≠ q): is_coprime p.val q.val := by
  have p_prime := p.property; have q_prime := q.property
  intro a ⟨h4, h5⟩
  replace p_prime := p_prime.right a h4
  replace q_prime := q_prime.right a h5
  cases p_prime with
  | inl a_eq => exact a_eq
  | inr a_eq => {
    cases q_prime with
    | inl a_eq => exact a_eq
    | inr a_eq2 => {
      have equal : p.val = q.val := Eq.trans a_eq.symm a_eq2
      exact False.elim <| h1 <| Subtype.eq equal
    }
  }
