import Game.Metadata

World "World2"
Level 7

Title "Hello World"

Introduction "This level introduces epimorhisms."

open CategoryTheory Category Function

variable (α β : Type) (f : α ⟶ β)

-- set_option trace.Meta.Tactic.simp.rewrite true


theorem injective_comp_right_iff_surjective {γ : Type*} [Nontrivial γ] :
    Injective (fun g : β → γ ↦ g ∘ f) ↔ Surjective f := by
  refine ⟨not_imp_not.mp fun not_surj inj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (fun x => x.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ ↦ c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]

instance instNontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

example : Epi f ↔ Function.Surjective f := by
  refine ⟨?_, ?_⟩
  · refine not_imp_not.mp fun not_surj inj ↦ not_subsingleton ℕ ⟨fun c c' ↦ ?_⟩
    have ⟨b₀, hb⟩ := not_forall.mp not_surj
    classical have := inj.left_cancellation (fun _ ↦ c) ((if · = b₀ then c' else c)) ?_
    · simpa using congr_fun this b₀
    ext a;
    classical change (fun g => g ∘ f) (fun x => c) a = (fun g => g ∘ f) (fun x => if x = b₀ then c' else c) a
    simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]
  · refine (fun hf => ⟨fun g g' h => ?_⟩)
    refine funext ?_
    refine hf.forall.2 ?_
    refine congr_fun h

Statement :  Epi f ↔ Function.Surjective f := by
  refine ⟨?_, ?_⟩
  · refine not_imp_not.mp fun not_surj inj ↦ not_subsingleton ℕ ⟨fun c c' ↦ ?_⟩
    have ⟨b₀, hb⟩ := not_forall.mp not_surj
    classical have := inj.left_cancellation (fun _ ↦ c) ((if · = b₀ then c' else c)) ?_
    · simpa using congr_fun this b₀
    ext a;
    classical change (fun g => g ∘ f) (fun x => c) a = (fun g => g ∘ f) (fun x => if x = b₀ then c' else c) a
    simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]
  · refine (fun hf => ⟨fun g g' h => ?_⟩)
    refine funext ?_
    refine hf.forall.2 ?_
    refine congr_fun h
