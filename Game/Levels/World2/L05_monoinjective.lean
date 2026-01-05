import Game.Metadata

World "World2"
Level 5

Title "Hello World"

Introduction "This level introduces epimorhisms."

open CategoryTheory Category

variable (α β : Type) (f : α ⟶ β)

example : Mono f ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono f).mp h
  · exact fun H => ⟨fun g g' h => H.comp_left h⟩

Statement : Mono f ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono f).mp h
  · exact fun H => ⟨fun g g' h => H.comp_left h⟩

NewDefinition homOfElement Function.Injective

NewTheorem CategoryTheory.homOfElement_eq_iff Function.Injective.comp_left
