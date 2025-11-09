
import Game.Metadata

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

World "MonoidWorld"
Level 16

Title "CommMOnoid Prod eq"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open Fin Function Finset
variable (α β γ : Type) [CommMonoid β]

example (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ y ∈ t, ∏ x ∈ s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => Finset.mem_product.trans and_comm


/-- Define a commutative monoid structure on ℕ using multiplication. -/
Statement (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ y ∈ t, ∏ x ∈ s, f (x, y) := by
  exact prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => Finset.mem_product.trans and_comm

Conclusion "This last message appears if the level is solved."
