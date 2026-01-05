import Game.Metadata

World "World2"
Level 5

Title "Hello World"

Introduction "This level introduces epimorhisms."

open CategoryTheory Category Function

variable (α β : Type) (f : α ⟶ β)

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
    obtain ⟨b₀, hb⟩ := not_forall.mp not_surj
    classical have := inj.left_cancellation (fun _ ↦ c) ((if · = b₀ then c' else c)) ?_
    · simpa using congr_fun this b₀
    ext a;
    classical change (fun g => g ∘ f) (fun x => c) a = (fun g => g ∘ f) (fun x => if x = b₀ then c' else c) a
    simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]
  · refine (fun hf => ⟨fun g g' h => ?_⟩)
    refine funext ?_
    refine hf.forall.2 ?_
    refine congr_fun h

NewDefinition Nontrivial Subsingleton Iff.mp Iff.mpr congr_fun Function.Surjective

NewTheorem Function.Surjective.forall if_neg Function.comp_apply funext Classical.not_forall
           not_subsingleton
