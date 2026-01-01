import Game.Metadata

World "World2"
Level 6

Title "Hello World"

Introduction "This level introduces epimorhisms."

open CategoryTheory Category

variable (α β : Type) (f : α ⟶ β)

example : Mono f ↔ Function.Injective f := by
  refine ⟨?_, ?_⟩
  -- define x₁ and x₂, show that x₁ = x₂ by f mono and f a₁ = f a₂
  · intro ⟨h⟩ a₁ a₂ hf
    let x₁ : Unit ⟶ α := fun _ => a₁
    let x₂ : Unit ⟶ α := fun _ => a₂
    -- Try refine h x₁ x₂ ?_
    -- Try ext
    have : x₁ = x₂ := h x₁ x₂ (by ext u; exact hf)
    -- Try using congr_fun
    exact congr_fun this ()
  · intro h; refine ⟨fun g k hf => ?_⟩
    -- Try ext a
    ext a
    -- Try refine h ?_
    exact h (congr_fun hf a)

Statement : Mono f ↔ Function.Injective f := by
  refine ⟨?_, ?_⟩
  · Hint "Try `intro ⟨h⟩ a₁ a₂ hf`"
    intro ⟨h⟩ a₁ a₂ hf
    Hint "Define x₁ that maps `()` to a₁ and x₂ that maps `()` to a₂
    Show that x₁ = x₂ using the fact that f is a monomorphism and f a₁ = f a₂
    "
    let x₁ : Unit ⟶ α := fun _ => a₁
    let x₂ : Unit ⟶ α := fun _ => a₂
    have : x₁ = x₂ := by
      Hint "Try `refine h x₁ x₂ ?_`"
      refine h x₁ x₂ ?_
      Hint "Try `ext unit`. `u` represents unit."
      ext u
      exact hf
    exact congr_fun this ()
  · intro h; refine ⟨fun g k hf => ?_⟩
    ext a
    exact h (congr_fun hf a)
