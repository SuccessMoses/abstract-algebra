import GameServer

-- import Mathlib.CategoryTheory.Iso
-- import Mathlib.CategoryTheory.Opposites

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

universe u

class Quiver' (C : Type u) where
  Hom (X : C) (Y : C) : Type

class Category' (C : Type u) extends Quiver' (C : Type u) where
  id X : Hom X X
  comp {X Y Z : C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  id_comp {X Y : C} {f : Hom X Y} : comp (id X) f = f
  comp_id {X Y : C} {f : Hom X Y} : comp f (id Y) = f
  assoc {W X Y Z : C} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W) :
    comp f (comp g h) = comp (comp f g) h

class Groupoid' (C : Type) extends Category' C where
  inv : ∀ {X Y : C}, (Hom X Y) → (Hom Y X)
  inv_comp : ∀ {X Y : C} (f : Hom X Y), comp (inv f) f = id Y
  comp_inv : ∀ {X Y : C} (f : Hom X Y), comp f (inv f) = id X

attribute [simp] Category'.id_comp Category'.comp_id Category'.assoc

infixr:10 " ⟶ " => Quiver'.Hom

notation "𝟙" => Category'.id  -- type as \b1

infixr:80 " ≫ " => Category'.comp -- type as \gg

----------------------- Functor ----------------------------------------

variable {C D E : Type} [Category' C] [Category' D] [Category' E]

structure Functor' (C : Type) [Category' C] (D : Type) [Category' D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by cat_disch
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫  g) = map f ≫ map g :=
    by cat_disch

infixr:26 " ⥤ " => Functor'

structure Comma (F : D ⥤ C) (G : E ⥤ C) where
  d : D
  e : E
  f : (F.obj d) ⟶ (G.obj e)

structure Square {F : D ⥤ C} {G : E ⥤ C} (X Y : Comma F G) where
  h : X.d ⟶ Y.d
  k : X.e ⟶ Y.e
  w : F.map h ≫ Y.f = X.f ≫ G.map k

@[ext]
theorem Square.ext {F : D ⥤ C} {G : E ⥤ C} {X Y : Comma F G}
  (s₁ s₂ : Square X Y)
  (h_h : s₁.h = s₂.h)
  (h_k : s₁.k = s₂.k) : s₁ = s₂ := by
  cases s₁
  cases s₂
  simp_all

attribute [simp] Square.w

-------------------------------------------------------------------

structure Slice (C : Type) [Category' C] (c : C) where
  x : C
  obj : c ⟶ x

structure Triangle {C : Type} [Category' C] {x : C} (f g : Slice C x) where
  h : Quiver'.Hom f.x g.x
  naturality : f.obj ≫ h = g.obj
