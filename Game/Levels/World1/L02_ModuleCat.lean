import Game.Metadata

World "World1"
Level 2

Title "Hello World"

Introduction "This level introduces ModuleCat "

open CategoryTheory

variable {R : Type} [Ring R]

example : Category (ModuleCat R) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun M N => M →ₗ[R] N
  · exact fun _ => LinearMap.id
  · exact fun f g => g ∘ₗ f
  · aesop
  · aesop
  · aesop

Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
: Category (ModuleCat R) := by
  · exact fun M N => M →ₗ[R] N
  · exact fun _ => LinearMap.id
  · exact fun f g => g ∘ₗ f
  · aesop
  · aesop
  · aesop

NewDefinition LinearMap LinearMap.id LinearMap.comp ModuleCat
