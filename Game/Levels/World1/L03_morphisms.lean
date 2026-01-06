import Game.Metadata

World "World1"
Level 3

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open CategoryTheory Category

variable (C : Type) [Category C] {X Y : C}

example (f : X ⟶ Y) (g h : Y ⟶ X) (h₁ : g ≫ f = 𝟙 _) (h₂ : f ≫ h = 𝟙 _) : g = h := by
  rw [←comp_id g, ←h₂, ←assoc, h₁, id_comp]

Statement (f : X ⟶ Y) (g h : Y ⟶ X) (h₁ : g ≫ f = 𝟙 _) (h₂ : f ≫ h = 𝟙 _) : g = h := by
  rw [←comp_id g, ←h₂, ←assoc, h₁, id_comp]

NewTheorem CategoryTheory.Category.assoc CategoryTheory.Category.id_comp
CategoryTheory.Category.comp_id
