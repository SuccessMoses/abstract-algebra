import Game.Metadata
import Game.Levels.World3.L07_comma
import Game.Levels.World1.L05_slice_category

World "World3"
Level 8

Title "Hello World"

Introduction "This level introduces the `CAT` category"

open CategoryTheory

variable {C : Type} [Category C] {c : C}

example : Comma (Functor.fromPUnit.{0} c) (𝟭 _) ⥤ Slice _ c := by
  refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}
  · refine fun ⟨h, k, f⟩ => ⟨?_, ?_⟩
    · exact k
    · simpa
  · rintro X Y ⟨h, k⟩
    dsimp
    refine Triangle.mk ?_ ?_
    · dsimp
      exact k
    · aesop
  · aesop
  · aesop

Statement
(preamble := refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_})
: Comma (Functor.fromPUnit.{0} c) (𝟭 _) ⥤ Slice _ c := by
  · refine fun ⟨h, k, f⟩ => ⟨?_, ?_⟩
    · exact k
    · simpa
  · rintro X Y ⟨h, k⟩
    dsimp
    refine Triangle.mk ?_ ?_
    · dsimp
      exact k
    · aesop
  · aesop
  · aesop
