import Game.Metadata

World "World3"
Level 7

Title "Hello World"

Introduction "This level introduces the `CAT` category"

open CategoryTheory

variable {C D E : Type} [Category C] [Category D] [Category E]
variable (F : D ⥤ C) (G : E ⥤ C)

-- set_option trace.aesop true

example : Category (Comma F G) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun X Y => CommaMorphism X Y
  · refine fun X => ⟨𝟙 _, 𝟙 _, ?_⟩
    -- rw [Functor.map_id, Functor'.map_id, id_comp, comp_id]
    aesop
  · refine fun ⟨h, k, nat₁⟩ ⟨h', k', nat₂⟩ => ⟨h ≫ h', k ≫ k', ?_⟩
    rw [F.map_comp, Category.assoc, nat₂, ←Category.assoc, nat₁, G.map_comp, Category.assoc]
  · aesop
  · aesop
  · aesop

Statement
(preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
: Category (Comma F G) := by
  · exact fun X Y => CommaMorphism X Y
  · refine fun X => ⟨𝟙 _, 𝟙 _, ?_⟩
    -- rw [Functor.map_id, Functor'.map_id, id_comp, comp_id]
    aesop
  · refine fun ⟨h, k, nat₁⟩ ⟨h', k', nat₂⟩ => ⟨h ≫ h', k ≫ k', ?_⟩
    rw [F.map_comp, Category.assoc, nat₂, ←Category.assoc, nat₁, G.map_comp, Category.assoc]
  · aesop
  · aesop
  · aesop

NewDefinition CategoryTheory.Comma CategoryTheory.CommaMorphism

NewTheorem CategoryTheory.Functor.map_comp
