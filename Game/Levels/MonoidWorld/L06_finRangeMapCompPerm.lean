import Game.Metadata

World "MonoidWorld"
Level 6

Title "finRange_map_comp_perm"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List
variable (n : ℕ) (α : Type) (x : (Fin n) → α) (σ : Equiv.Perm (Fin n))

example : (finRange n).map (x ∘ σ) ~ (finRange n).map x := by
  rw [← map_map]
  apply Perm.map
  exact Equiv.Perm.map_finRange_perm σ

/-- (finRange n).map (x ∘ σ) ~ (finRange n).map x -/
Statement : (finRange n).map (x ∘ σ) ~ (finRange n).map x := by
  rw [← map_map]
  apply Perm.map
  exact Equiv.Perm.map_finRange_perm σ

Conclusion "This last message appears if the level is solved."
