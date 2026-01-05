import Game.Metadata

World "World3"
Level 2

Title "Hello World"

Introduction "This level introduces the C(-, c) : Cᵒᵖ ⥤ Type"

open CategoryTheory

variable {C : Type} [Category C]

example (c : C) : Cᵒᵖ ⥤ Type := by
  refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}
  · exact fun x => x.unop ⟶ c
  · exact fun f g => f.unop ≫ g
  · aesop
  · aesop

Statement (preamble := refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}) (c : C) : Cᵒᵖ ⥤ Type := by
  · exact fun x => x.unop ⟶ c
  · exact fun f g => f.unop ≫ g
  · aesop
  · aesop
