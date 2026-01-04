import Game.Metadata
import Game.Levels.World3.L07_comma
import Game.Levels.World1.L05_slice_category

World "World3"
Level 10

Title "Hello World"

Introduction "This level introduces the `CAT` category"

instance : Category' PUnit := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun x y => PLift <| x = y
  · exact fun _ => PLift.up <| rfl
  · refine fun {X Y Z} g f => ?_
    cases X
    cases Y
    cases Z
    exact g
  · aesop
  · aesop
  · aesop

variable {C : Type} [Category' C] (c : C)

def const (X : C) : PUnit ⥤ C where
  obj _ := X
  map _ := 𝟙 _

def id_functor : C ⥤ C where
  obj X := X
  map f := f

@[simp]
theorem const_eq (X : C) (p : PUnit) : (const X).obj p = X := by
  cases p
  rfl

@[simp]
theorem id_functor_eq (X : C) : id_functor.obj X = X := rfl

@[simp]
theorem const_map (X : C) {p q : PUnit} (f : p ⟶ q) : (const X).map f = 𝟙 X := by
  cases p
  cases q
  rfl

@[simp]
theorem id_functor_map {X Y : C} (f : X ⟶ Y) : id_functor.map f = f := rfl

notation "𝟭" => id_functor

example : Comma (const c) 𝟭 ⥤ Slice _ c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine fun ⟨h, k, f⟩ => ⟨?_, ?_⟩
    · exact k
    · rw [id_functor_eq, const_eq] at f
      exact f
  · rintro X Y ⟨h, k⟩
    dsimp
    refine Triangle.mk ?_ ?_
    · dsimp
      exact k
    · aesop
      rw [] at w
  · aesop
  · aesop







example : Category' (Comma F G) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun X Y => Square X Y
  · refine fun X => ⟨𝟙 _, 𝟙 _, ?_⟩
    rw [Functor'.map_id, Functor'.map_id, id_comp, comp_id]
  · refine fun ⟨h, k, nat₁⟩ ⟨h', k', nat₂⟩ => ⟨h ≫ h', k ≫ k', ?_⟩
    rw [F.map_comp, ←assoc, nat₂, assoc, nat₁, G.map_comp, assoc]
  · aesop
  · aesop
  · aesop

Statement
(preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
: Category' (Comma F G) := by
  · exact fun X Y => Square X Y
  · refine fun X => ⟨𝟙 _, 𝟙 _, ?_⟩
    rw [Functor'.map_id, Functor'.map_id, id_comp, comp_id]
  · refine fun ⟨h, k, nat₁⟩ ⟨h', k', nat₂⟩ => ⟨h ≫ h', k ≫ k', ?_⟩
    rw [F.map_comp, ←assoc, nat₂, assoc, nat₁, G.map_comp, assoc]
  · aesop
  · aesop
  · aesop
