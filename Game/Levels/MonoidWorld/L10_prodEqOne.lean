import Game.Metadata

World "MonoidWorld"
Level 10

Title "Prod of one eq one"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List
variable (n : ℕ) (M : Type) [Monoid M] (a : M) (l : List M)

example (h : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l
  · rfl
  · rw [List.prod_cons]
    have h₁ : tail.prod = 1 := by
      apply tail_ih
      intro x hx
      apply h
      exact mem_cons_of_mem _ hx
    have h₂ : head = 1 := by
      exact h head (mem_cons_self)
    rw [h₁, h₂, one_mul]

/-- Define a monoid structure on ℕ using addition. -/
Statement (h : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l
  · rfl
  · rw [List.prod_cons]
    have h₁ : tail.prod = 1 := by
      apply tail_ih
      intro x hx
      apply h
      exact mem_cons_of_mem _ hx
    have h₂ : head = 1 := by
      exact h head (mem_cons_self)
    rw [h₁, h₂, one_mul]

Conclusion "This last message appears if the level is solved."
