import Game.Metadata

World "MonoidWorld"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable {M : Type} [Monoid M]

example (e : M) (h : ∀ m, e * m = m) : e = 1 := by
  rw [← mul_one e, h]

NewTactic rw apply

/-- `x ∈ A` means that `x` is an element of `A`.  To enter the symbol `∈`, type
`\mem` or `\in`. -/
DefinitionDoc mul_one as "ε"

NewDefinition mul_one

/-- Define a monoid structure on ℕ using addition. -/
Statement (e : M) (h : ∀ m, e * m = m) : e = 1 := by
  rw [← mul_one e, h]

Conclusion "This last message appears if the level is solved."
