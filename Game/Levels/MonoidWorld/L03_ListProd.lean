import Game.Metadata

World "MonoidWorld"
Level 3

Title "Instance of Monoid"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List
variable (M : Type) [Monoid M] (x : ℕ → M)

NewTheorem mul_assoc Nat.add_assoc List.prod_range_succ

NewDefinition List.range List.prod List.map

NewTactic induction simp

example (m n : ℕ) :
    ((range m).map x).prod * ((range n).map (fun v => x (m + v))).prod =
    ((range (m+n)).map x).prod := by
  induction n
  · simp
  · rw [prod_range_succ, ← mul_assoc (map x (range m)).prod, a, ← prod_range_succ]
    simp [Nat.add_assoc]

/-- Define a monoid structure on ℕ using addition. -/
Statement (m n : ℕ) :
    ((range m).map x).prod * ((range n).map (fun v => x (m + v))).prod =
    ((range (m+n)).map x).prod := by
  induction n
  · simp
  · rw [prod_range_succ, ← mul_assoc (map x (range m)).prod, a, ←prod_range_succ]
    simp [Nat.add_assoc]

Conclusion "This last message appears if the level is solved."
