import Game.Metadata

World "World3"
Level 6

Title "Hello World"

Introduction "This level introduces the `CAT` category"

open CategoryTheory

variable {G₁ : Type} [Group G₁] {G₂ : Type} [Group G₂]

example (f : G₁ →* G₂) : SingleObj G₁ ⥤ SingleObj G₂ := by
  refine {obj := ?_ , map := ?_, map_id := ?_, map_comp := ?_}
  · exact fun _ => default
  · exact ⇑f
  · exact fun _ => f.map_one
  · exact fun x y => f.map_mul y x

Statement
(preamble := refine {obj := ?_ , map := ?_, map_id := ?_, map_comp := ?_})
(f : G₁ →* G₂) : SingleObj G₁ ⥤ SingleObj G₂ := by
  · exact fun _ => default
  · exact ⇑f
  · exact fun _ => f.map_one
  · exact fun x y => f.map_mul y x
