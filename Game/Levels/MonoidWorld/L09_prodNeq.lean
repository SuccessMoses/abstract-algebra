import Game.Metadata

World "MonoidWorld"
Level 9

Title "List Prod ≠ 1"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable (M : Type) [Monoid M] (a : M) (l : List M)

example (h : l.prod ≠ 1) : 0 < l.length := by
  cases l
  ·  simp at h
  · rw [List.length_cons]
    simp

/-- l.prod ≠ 1 → |l| > 0. -/
Statement (h : l.prod ≠ 1) : 0 < l.length := by
  cases l
  ·  simp at h
  · rw [List.length_cons]
    simp

Conclusion "This last message appears if the level is solved."
