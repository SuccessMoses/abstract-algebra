-- import Game.Metadata
-- import Game.Levels.World2.L02_postcomposition

-- World "World2"
-- Level 3

-- Title "Hello World"

-- Introduction "The previous level proved that f : x ⟶ y is an isomorphism if and only if
-- f_* : C(c, x) → C(c, y) is a bijection. The second statement was that
-- f* : C(y, c) → C(x, c) is a bijection. This statement can be proven from the first using the
-- principle of dulaity. If a statement is true for a categories, then it is true in particular for
-- the opposite category Cᵒᵖ, hence we can derive from statements about C using a duality argument.
-- "

-- open CategoryTheory Opposite Function

-- section

-- abbrev fstar' {C : Type} [Category C] {x y : C} (f : x ⟶ y) (c : C) : (y ⟶ c) → (x ⟶ c) :=
--   fun g => f ≫ g

-- variable {C : Type} [Category C] {x y : C} (f : x ⟶ y)

-- example : IsIso f ↔ ∀ c : C, HasInverse (fstar' f c) := by
--   obtain h := t1 f.op
--   sorry
