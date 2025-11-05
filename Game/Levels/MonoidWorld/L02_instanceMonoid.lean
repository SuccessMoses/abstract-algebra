import Game.Metadata

World "MonoidWorld"
Level 2

Title "Instance of Monoid"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

NewTactic exact

NewDefinition Nat.mul_assoc Nat.one_mul Nat.mul_one Nat.mul

/-- Define a monoid structure on ℕ using addition. -/
Statement (preamble := refine { mul := ?_ ,one := ?_, mul_one := ?_, one_mul := ?_, mul_assoc := ?_ }) :
  Monoid ℕ := by
  · exact Nat.mul
  · exact Nat.mul_assoc
  · exact 1
  · exact Nat.one_mul
  · exact Nat.mul_one

Conclusion "This last message appears if the level is solved."
