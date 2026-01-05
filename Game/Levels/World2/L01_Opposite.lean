import Game.Metadata

World "World2"
Level 1

Title "Hello World"

Introduction "This level introduces the opposite category."

open CategoryTheory Opposite

example {C : Type} [Category C] : Category (Opposite C) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun X Y => Y.unop ⟶ X.unop
  · exact fun X => 𝟙 X.unop
  · exact fun f g => g ≫ f
  · exact Category.comp_id
  · exact Category.id_comp
  · exact fun _ _ _ => Eq.symm (Category.assoc _ _ _)

Statement (preamble := refine { Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    {C : Type} [Category C] {x : C} : Category (Opposite C) := by
  · exact fun X Y => Y.unop ⟶ X.unop
  · exact fun X => 𝟙 X.unop
  · exact fun f g => g ≫ f
  · exact Category.comp_id
  · exact Category.id_comp
  · exact fun _ _ _ => Eq.symm (Category.assoc _ _ _)
