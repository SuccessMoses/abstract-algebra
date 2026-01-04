import Game.Metadata

World "World1"
Level 6

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open CategoryTheory

variable {α : Type} [Preorder α]

example : Category' α := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun u v => PLift (u ≤ v)
  · exact fun _ => ⟨le_refl _⟩
  · exact fun ⟨f⟩ ⟨g⟩ => ⟨le_trans f g⟩
  · cat_disch
  · cat_disch
  · cat_disch

Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}):
Category' (Unit) := by
  · exact fun u v => PLift (u ≤ v)
  · exact fun _ => ⟨le_refl _⟩
  · exact fun ⟨f⟩ ⟨g⟩ => ⟨le_trans f g⟩
  · cat_disch
  · cat_disch
  · cat_disch
