import Game.Metadata

World "World1"
Level 2

Title "Hello World"

Introduction "This level introduces ModuleCat "

open CategoryTheory

variable {R : Type} [Ring R]

/--
`Vectₖ` is the category whose objects are `R`-modules and whose morphisms
are `R`-linear maps.
-/
Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
: Category (ModuleCat R) := by
  · exact fun M N => M →ₗ[R] N
  · exact fun _ => LinearMap.id
  · exact fun f g => g ∘ₗ f
  · aesop
  · aesop
  · aesop

NewDefinition LinearMap LinearMap.id LinearMap.comp ModuleCat

#check ModuleCat.of
#check ModuleCat.ofHom

/--
`ModuleCat R` where R is a ring is the category whose objects are modules over R and morphism
between M and N is a linear map.

`ModuleCat.of` is the preferred way to construct a term of `ModuleCat R`.

`ModuleCat.ofHom` is constructs a morphism of `ModuleCat R` from a linear map.
-/
TheoremDoc ModuleCat as "ModuleCat"
