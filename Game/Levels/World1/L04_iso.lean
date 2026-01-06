import Game.Metadata

World "World1"
Level 4

Title "Hello World"

Introduction "This level introduces Isomorphisms."

open CategoryTheory Category Iso

variable {C : Type} [Category C] (X Y : C) (α β : X ≅ Y)

example (h : α.hom = β.hom) : α.inv = β.inv := by
  rw [←comp_id α.inv, ←hom_inv_id β, ←assoc, ←h, inv_hom_id α, id_comp]

Statement (h : α.hom = β.hom) : α.inv = β.inv := by
  rw [←comp_id α.inv, ←hom_inv_id β, ←assoc, ←h, inv_hom_id α, id_comp]

NewTheorem CategoryTheory.Iso.hom_inv_id CategoryTheory.Iso.inv_hom_id

NewDefinition CategoryTheory.inv CategoryTheory.IsIso
