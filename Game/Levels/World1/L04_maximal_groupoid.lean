import Game.Metadata

World "World1"
Level 4

Title "Hello World"

Introduction "This level introduces the groupoid and the maximal groupoid."

open CategoryTheory Category Iso

structure MaximalGroupoid (C : Type) where
  of : C

example {C : Type} [Category C] : Category' (MaximalGroupoid C) := by
  refine { Hom := ?_, id := ?_, comp := ?_}
  · exact fun X Y => X.of ≅ Y.of
  · exact fun X => Iso.refl X.of
  exact fun f g => Iso.trans f g

Statement (preamble := refine { Hom := ?_, id := ?_, comp := ?_}) {C : Type} [Category C] : Category' (MaximalGroupoid C) := by
  · exact fun X Y => X.of ≅ Y.of
  · exact fun X => Iso.refl X.of
  exact fun f g => Iso.trans f g
