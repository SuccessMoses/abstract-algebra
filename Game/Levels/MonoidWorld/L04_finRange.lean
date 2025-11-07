import Game.Metadata

World "MonoidWorld"
Level 4

Title "FinRange succ"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List
variable (n : ℕ)

example : finRange (n+1) = 0 :: (finRange n).map Fin.succ := by
  apply List.ext_getElem
  · simp
  · intro i
    cases i <;> simp

/-- finRange (n+1) = 0 :: (finRange n).map Fin.succ -/
Statement : finRange (n+1) = 0 :: (finRange n).map Fin.succ := by
  apply List.ext_getElem
  · simp
  · intro i
    cases i <;> simp

Conclusion "This last message appears if the level is solved."
