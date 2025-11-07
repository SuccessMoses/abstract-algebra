import Game.Metadata

World "MonoidWorld"
Level 5

Title "Equiv.Perm.map_finRange_perm"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

open List
variable {n : ℕ} (σ : Equiv.Perm (Fin n))

example : map σ (finRange n) ~ finRange n := by
  have h :
    map (σ) (finRange n) ~ finRange n ↔
      ∀ (a : Fin n), a ∈ (map (σ) (finRange n)) ↔ a ∈ finRange n := by
      apply perm_ext_iff_of_nodup
      · exact List.Nodup.map σ.injective (nodup_finRange n)
      · exact nodup_finRange n
  simp [h, mem_map]
  apply Equiv.surjective at σ
  rw [Function.Surjective] at σ
  assumption
  -- simpa [h, mem_map] using σ.surjective could close this


/-- map σ (finRange n) ~ finRange n -/
Statement : map σ (finRange n) ~ finRange n := by
  have h :
    map (σ) (finRange n) ~ finRange n ↔
      ∀ (a : Fin n), a ∈ (map (σ) (finRange n)) ↔ a ∈ finRange n := by
      apply perm_ext_iff_of_nodup
      · exact List.Nodup.map σ.injective (nodup_finRange n)
      · exact nodup_finRange n
  simp [h, mem_map]
  apply Equiv.surjective at σ
  rw [Function.Surjective] at σ
  assumption

Conclusion "This last message appears if the level is solved."
