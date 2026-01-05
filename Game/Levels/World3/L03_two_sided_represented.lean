import Game.Metadata

World "World3"
Level 3

Title "Hello World"

Introduction "This level introduces the C(-, -) functor."

open CategoryTheory

variable {C : Type} [Category C] {D : Type} [Category D]

#synth Category (C × D)

example : Cᵒᵖ × C ⥤ Type := by
  refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}
  · exact fun (x, y) => x.unop ⟶ y
  · refine fun (f, h) g => f.unop ≫ g ≫ h
  · aesop
  · aesop

Statement
    (preamble := refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}) :
    Cᵒᵖ × C ⥤ Type := by
  · exact fun (x, y) => x.unop ⟶ y
  · exact fun (f, h) g => f.unop ≫ g ≫ h
  · aesop
  · aesop

NewDefinition Prod
