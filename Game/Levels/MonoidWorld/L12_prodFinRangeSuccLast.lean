import Game.Metadata

World "MonoidWorld"
Level 12

Title "prod_finRange_succ_last"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable {M : Type*} [Monoid M] {n : ℕ} (f : Fin n.succ → M)
open List Fin

example :
    ((finRange n.succ).map f).prod = ((finRange n).map (f ∘ castSucc)).prod * f (Fin.last n) := by
  rw [List.finRange_succ_last, map_append, map_singleton, map_map, prod_append, prod_singleton]

/-- ((finRange n.succ).map f).prod = ((finRange n).map (f ∘ castSucc)).prod * f (Fin.last n). -/
Statement :
    ((finRange n.succ).map f).prod = ((finRange n).map (f ∘ castSucc)).prod * f (Fin.last n) := by
  rw [List.finRange_succ_last, map_append, map_singleton, map_map, prod_append, prod_singleton]

Conclusion "This last message appears if the level is solved."
