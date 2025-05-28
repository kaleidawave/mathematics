import Mathematics.Structures.Set
import Mathematics.Structures.Set.Operations
import Mathematics.Structures.Set.Theorems
import Mathematics.Structures.Set.BigUnion

-- https://adam.math.hhu.de/#/g/djvelleman/stg4/world/FamInter/level/0
def BigIntersection {T: Type} (U: Set (Set T)): Set T := fun x => ∀s ∈ U, x ∈ s

notation "⋂₀ " F:100 => BigIntersection F

-- TODO move
def Set.image {T U: Type} (S: Set T) (f: T → U): Set U := fun y => ∃x ∈ S, f x = y
def NonEmpty {T: Type} (s: Set T): Prop := ∃x: T, x ∈ s

theorem Set.image_image {T U V: Type} (S: Set T) (f: T → U) (g: U → V): (Set.image S f).image g = Set.image S (g ∘ f) := by
  ext x
  constructor
  {
    intro h1
    obtain ⟨gx, h1⟩ := h1
    obtain ⟨fx, h2⟩ := h1.left
    exists fx
    constructor
    exact h2.left
    simp
    rw [h2.right]
    exact h1.right
  }
  {
    intro h1
    obtain ⟨gfx, h1⟩ := h1
    exists f gfx
    constructor
    {
      exists gfx
      constructor
      exact h1.left
      rfl
    }
    exact h1.right
    -- exists gfx
  }

theorem UnionComplement {T: Type} (F : Set (Set T)): (⋃₀ F)ᶜ = ⋂₀ (fun s => sᶜ ∈ F) := by
  ext a
  constructor
  {
    intro h1 t h2
    change tᶜ ∈ F at h2
    change a ∈ (⋃₀ F)ᶜ at h1
    rw [complement.mem] at h1
    apply Classical.byContradiction
    intro h3
    apply h1
    exists tᶜ
  }
  {
    intro h1 h2
    change a ∈ (⋃₀ F) at h2
    obtain ⟨x, h2⟩ := h2
    specialize h1 (xᶜ)
    apply h1
    change (xᶜ)ᶜ ∈ F
    rw [complement.complement]
    exact h2.left
    exact h2.right
  }

-- https://adam.math.hhu.de/#/g/djvelleman/stg4/world/FamCombo/level/1

theorem NotBigUnion {T: Type} {U: Set (Set T)} {x: T} (h1: ¬(x ∈ ⋂₀ U)):
  ∃Uₐ ∈ U, x ∉ Uₐ
:= by
  change ¬(∀x, _) at h1
  have ⟨l, r⟩ := Classical.not_forall.mp h1
  exists l
  exact Classical.not_imp_iff_and_not.mp r

theorem BigIntersection.intersection {T: Type} (X: Set T) (U: Set (Set T)) (uNE: NonEmpty U):
  ⋂₀ (U.image fun Uₐ => X ∩ Uₐ) = X ∩ (⋂₀ U)
:= by
  ext x
  constructor
  {
    intro h1
    obtain ⟨u, h2⟩ := uNE
    constructor
    {
      have d : (X ∩ u ∈ U.image fun Uₐ => X ∩ Uₐ) := by exists u
      specialize h1 (X ∩ u) d
      exact h1.left
    }
    {
      intro u2 h2
      have d : (X ∩ u2 ∈ U.image fun Uₐ => X ∩ Uₐ) := by exists u2
      specialize h1 (X ∩ u2) d
      exact h1.right
    }
  }
  {
    intro h1 r h2
    obtain ⟨l, h2⟩ := h2
    rw [←h2.right]
    constructor
    exact h1.left
    exact h1.right l h2.left
  }

theorem DM1 {T: Type} (X: Set T) (U: Set (Set T)) :
  ⋃₀ U.image (fun Uₐ => X \ Uₐ) = X \ (⋂₀ U)
:= by
  rw [difference_as_intersection]
  conv => enter [1, 1, x, 2, u]; rw [difference_as_intersection]
  change (⋃₀ U.image (fun u => X ∩ (uᶜ))) = X ∩ ((⋂₀ U)ᶜ)

  ext x
  constructor
  {
    intro ⟨a, ⟨⟨b, h2⟩, r⟩⟩
    have ⟨l, h3⟩ := h2
    rw [←h3] at r
    constructor
    exact r.left
    {
      intro h4
      have ⟨_, h5⟩ := r
      specialize h4 b l
      exact h5 h4
    }
  }
  {
    intro ⟨xInX, xInIntC⟩
    obtain ⟨U, xNeU⟩ := NotBigUnion xInIntC
    exists X ∩ (Uᶜ)
    symm
    constructor
    {
      constructor
      exact xInX
      have : x ∈ Uᶜ := by exact (complement.mem x U).mpr xNeU.right
      exact this
    }
    {
      exists U
      constructor
      exact xNeU.left
      rfl
    }
  }

theorem DM2 {T: Type} (X: Set T) (U: Set (Set T)) (uNE: NonEmpty U):
  ⋂₀ (U.image fun Uₐ => X \ Uₐ) = X \ (⋃₀ U)
:= by
  rw [difference_as_intersection, UnionComplement]
  conv => enter [1, 1, x, 2, u]; rw [difference_as_intersection]

  obtain ⟨u, h1⟩ := uNE
  have d := BigIntersection.intersection X (U.image fun x => xᶜ) (⟨uᶜ, by exists u⟩)
  rw [Set.image_image] at d

  conv at d => {
    lhs;
    rhs;
    rhs;
    change fun Uₐ => X ∩ (Uₐᶜ)
  }

  conv => {
    lhs;
    rhs;
    change U.image (fun Uₐ => X ∩ (Uₐᶜ))
  }

  -- TODO messy
  have e: (⋂₀ U.image fun x => xᶜ) = ⋂₀ fun s => sᶜ ∈ U := by
    ext a
    constructor
    {
      intro h1 S h2
      specialize h1 S
      change Sᶜ ∈ U at h2
      apply h1
      exists Sᶜ
      constructor
      exact h2
      change Sᶜᶜ = S
      exact complement.complement S
    }
    {
      intro h1 S h2
      specialize h1 S
      apply h1
      change Sᶜ ∈ U
      obtain ⟨n, h2⟩ := h2
      rw [←h2.right]
      change nᶜᶜ ∈ U
      rw [complement.complement]
      exact h2.left
    }

  rw [←e]
  exact d

theorem BigUnionEmpty {T: Type} : ⋃₀ (Set.empty (Set T)) = Set.empty T := by
  ext a
  constructor
  {
    intro ⟨l, h1⟩
    have : False := h1.left
    trivial
  }
  {
    intro h1
    contradiction
  }

theorem BigIntersectionEmpty {T: Type} : ⋂₀ (Set.empty (Set T)) = Set.universal T := by
  ext a
  constructor
  {
    intro h1
    trivial
  }
  {
    intro _ s sInEmpty
    contradiction
  }
