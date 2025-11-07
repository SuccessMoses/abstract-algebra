import Game.Metadata

World "MonoidWorld"
Level 8

Title "Prod concat"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable (M : Type) [Monoid M] (a : M) (l : List M)

example : (l.concat a).prod = l.prod * a := by
  rw [List.concat_eq_append, List.prod_append, List.prod_singleton]

/-- (l.concat a).prod = l.prod * a -/
Statement : (l.concat a).prod = l.prod * a := by
  rw [List.concat_eq_append, List.prod_append, List.prod_singleton]

Conclusion "This last message appears if the level is solved."
