import Game.Metadata

World "MonoidWorld"
Level 11

Title "finRange succ"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List Fin
variable (n : ℕ) (M : Type) [Monoid M] (a : M) (l : List M) (f : (Fin (n.succ)) -> M)

theorem finRange_succ' :
    ((finRange n.succ).map f).prod = f 0 * ((finRange n).map fun i ↦ f i.succ).prod := by
  rw [finRange_succ_eq_map]
  simp [Function.comp_def]

/-- ((finRange n.succ).map f).prod = f 0 * ((finRange n).map fun i ↦ f i.succ).prod -/
Statement :
    ((finRange n.succ).map f).prod = f 0 * ((finRange n).map fun i ↦ f i.succ).prod := by
  rw [finRange_succ_eq_map]
  simp [Function.comp_def]

Conclusion "This last message appears if the level is solved."
