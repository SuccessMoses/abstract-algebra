import Game.Metadata

World "World3"
Level 4

Title "Hello World"

Introduction "This level introduces the `CAT` category"

open CategoryTheory

example : Category Type := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun α β => α → β
  · exact fun _ => id
  · exact fun f g => g ∘ f
  · exact fun _ => Function.id_comp _
  · exact fun _ => Function.comp_id _
  · exact fun _ _ _ => Function.comp_assoc _ _ _

Statement
(preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}) :
Category Type := by
  · exact fun α β => α → β
  · exact fun _ => id
  · exact fun f g => g ∘ f
  · exact fun _ => Function.id_comp _
  · exact fun _ => Function.comp_id _
  · refine fun _ _ _ => ?_
    exact Function.comp_assoc _ _ _

NewDefinition id

NewTheorem Function.comp_assoc Function.id_comp Function.comp_id
