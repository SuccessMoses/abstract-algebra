import Game.Metadata

World "MonoidWorld"
Level 7

Title "Prod singleton"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable (M : Type) [Monoid M] (a : M)

-- [a].prod is definitionally equal to a * 1, hence it suffice to show a * 1 = a
example : [a].prod = a := by
  apply mul_one

/-- [a].prod = a -/
Statement : [a].prod = a := by
  apply mul_one

Conclusion "This last message appears if the level is solved."
