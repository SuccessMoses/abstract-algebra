import Game.Metadata

World "World3"
Level 6

Title "Hello World"

Introduction "This level introduces the `CAT` category"

open CategoryTheory

variable {X : Type} {Y : Type} [Preorder X] [Preorder Y]

example {f : X → Y} (h : Monotone f) : X ⥤ Y := by
  refine {obj := ?_ , map := ?_, map_id := ?_, map_comp := ?_}
  · exact f
  · refine fun g => homOfLE (h g.le)
  · cat_disch
  · cat_disch

Statement
(preamble := refine {obj := ?_ , map := ?_, map_id := ?_, map_comp := ?_})
{f : X → Y} (h : Monotone f) : X ⥤ Y := by
  · exact f
  · refine fun g => homOfLE (h g.le)
  · cat_disch
  · cat_disch
