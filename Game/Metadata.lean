import GameServer

import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

-- import Mathlib.Tactic.Common

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels.
-/

open CategoryTheory

structure Slice (C : Type) [Category C] (c : C) where
  x : C
  obj : c ⟶ x

structure Triangle {C : Type} [Category C] {x : C} (f g : Slice C x) where
  h : f.x ⟶ g.x
  naturality : f.obj ≫ h = g.obj
