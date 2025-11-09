
import Game.Metadata

import Mathlib.Logic.Equiv.Defs

World "MonoidWorld"
Level 14

Title "CommMOnoid Prod eq"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List

variable (M : Type) (l₁ l₂ : List (Fin n)) (ψ : Equiv.Perm (Fin n))
variable (x : Fin n → M)

theorem finRange_comp_perm (σ : Equiv.Perm (Fin n)) : (finRange n).map (x ∘ σ) ~ (finRange n).map x := by
  rw [← map_map]
  apply Perm.map
  exact Equiv.Perm.map_finRange_perm σ

variable [CommMonoid M]

example : ((finRange n).map (x ∘ ψ)).prod = ((finRange n).map x).prod := by
  apply Perm.prod_eq
  apply finRange_comp_perm

/-- Define a commutative monoid structure on ℕ using multiplication. -/
Statement : ((finRange n).map (x ∘ ψ)).prod = ((finRange n).map x).prod := by
  apply Perm.prod_eq
  apply finRange_comp_perm

Conclusion "This last message appears if the level is solved."
