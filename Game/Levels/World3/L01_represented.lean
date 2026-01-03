import Game.Metadata

World "World3"
Level 1

Title "Hello World"

Introduction "This level introduces C(c, -) : C ⥤ Type. "

open CategoryTheory

variable {C : Type} [Category C]

example (c : C) : C ⥤ Type := by
  refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}
  · exact fun x => c ⟶ x
  · exact fun f g => g ≫ f
  · cat_disch
  · cat_disch

Statement (preamble := refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}) (c : C) : C ⥤ Type := by
  · exact fun x => c ⟶ x
  · exact fun f g => g ≫ f
  · cat_disch
  · cat_disch
