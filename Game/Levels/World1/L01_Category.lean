import Game.Metadata

World "World1"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open CategoryTheory

variable {G : Type} [Monoid G]

abbrev BG := SingleObj G

example : Category' (BG (G := G)) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun _ _ => G
  · exact fun _ => 1
  · exact fun x y => y * x
  · exact mul_one _
  · exact one_mul _
  · exact fun _ _ _ => mul_assoc _ _ _

Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    : Category' (Unit) := by
  · exact fun _ _ => G
  · exact fun _ => 1
  · exact fun x y => y * x
  · exact mul_one _
  · exact one_mul _
  · exact fun _ _ _ => mul_assoc _ _ _

NewTactic exact simp intro refine dsimp
NewDefinition Nat
NewTheorem Eq.symm Nat.add_assoc Category'.id Category'.assoc Category'.comp Category'.id_comp
           Category'.comp_id
