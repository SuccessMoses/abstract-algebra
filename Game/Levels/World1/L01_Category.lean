import Game.Metadata

World "World1"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

structure Quiver' (C : Type) where
  Hom (X : C) (Y : C) : Type

structure Category' (C : Type) extends Quiver' (C : Type) where
  -- Hom (X : C) (Y : C) : Type
  id X : Hom X X
  comp {X Y Z : C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z

example : Category' (Unit) := by
  refine {Hom := ?_, id := ?_, comp := ?_}
  · exact fun _ _ => Nat
  · exact fun _ => 0
  · exact (. + .)

Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_}) : Category' (Unit) := by
  · exact fun _ _ => Nat
  · exact fun _ => 0
  · exact (. + .)

NewTactic exact
NewDefinition Nat
