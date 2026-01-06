import Game.Metadata
import Game.Levels.World3.L09_dualfunctor

World "World4"
Level 1

Title "Hello World"

Introduction "This level introduces the dual functor"

open CategoryTheory Module

variable (R : Type) [CommRing R]

def doubleDual : ModuleCat R ⥤ ModuleCat R :=
  Functor.rightOp (dualfunctor R) ⋙ (dualfunctor R)

example : 𝟭 _ ⟶ (doubleDual R) := by
  refine {app := ?_, naturality := ?_}
  · refine fun X => ModuleCat.ofHom ?_
    exact Dual.eval R X
  · aesop

Statement
(preamble := refine {app := ?_, naturality := ?_})
: 𝟭 _ ⟶ (doubleDual R) := by
  · refine fun X => ModuleCat.ofHom ?_
    exact Dual.eval R X
  · aesop
