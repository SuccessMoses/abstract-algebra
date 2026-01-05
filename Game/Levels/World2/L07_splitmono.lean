import Game.Metadata

World "World2"
Level 7

Title "Hello World"

Introduction "This level introduces split monomorhisms."

open CategoryTheory

variable {C : Type} [Category C] {X Y : C} (f : X ⟶ Y)

example (sm : SplitMono f) : Mono f := by
  refine ⟨?_⟩
  refine fun  g h w => ?_
  replace w := w =≫ sm.retraction
  simpa using w

Statement (sm : SplitMono f) : Mono f := by
  refine ⟨?_⟩
  refine fun  g h w => ?_
  replace w := w =≫ sm.retraction
  simpa using w

NewDefinition SplitMono CategoryTheory.SplitMono.retraction IsSplitMono IsSplitMono.mk
