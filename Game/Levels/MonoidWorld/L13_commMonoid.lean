import Game.Metadata

World "MonoidWorld"
Level 13

Title "Instance of CommMonoid"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

NewTactic exact

NewDefinition Nat.mul_assoc Nat.one_mul Nat.mul_one Nat.mul Nat.mul_comm

/-- Define a commutative monoid structure on ℕ using multiplication. -/
Statement (preamble := refine { mul := ?_ ,one := ?_, mul_one := ?_, one_mul := ?_, mul_assoc := ?_, mul_comm := ?_ }) :
  CommMonoid ℕ := by
  · exact Nat.mul
  · exact 1
  · exact Nat.mul_one
  · exact Nat.one_mul
  · exact Nat.mul_assoc
  · exact Nat.mul_comm

Conclusion "This last message appears if the level is solved."
