import Game.Metadata

World "MonoidWorld"
Level 5

Title "Instance of Monoid"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

namespace Five

variable (M : Type) [Monoid M] (a : M) -- (x : ℕ → M) (ψ : ℕ → ℕ)

example : [a].prod = a * 1 := by rfl

-- [a].prod is definitionally equal to a * 1, hence it suffice to show a * 1 = a
theorem prod_singleton : [a].prod = a := by
  apply mul_one

theorem prod_concat (l : List M) : (l.concat a).prod = l.prod * a := by
  rw [List.concat_eq_append, List.prod_append, List.prod_singleton]

example (l : List M) (h : l.prod ≠ 1) : 0 < l.length := by
  cases l
  ·  simp at h
  · rw [List.length_cons]
    simp

example [Preorder M] (l : List M) (h : 1 < l.prod) : 0 < l.length := by
  cases l
  · simp at h
  · rw [List.length_cons]
    simp

open List
variable (l : List M)

theorem prod_range_succ (f : ℕ -> M) (n : ℕ) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ, map_append, prod_append, map_singleton, prod_singleton]

theorem prod_range_succ' (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i ↦ f i.succ).prod := by
  rw [range_succ_eq_map]
  simp [Function.comp_def]

theorem prod_eq_one (h : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l
  · rfl
  · rw [List.prod_cons]
    have h₁ : tail.prod = 1 := by
      apply tail_ih
      intro x hx
      apply h
      exact mem_cons_of_mem _ hx
    have h₂ : head = 1 := by
      exact h head (mem_cons_self)
    rw [h₁, h₂, one_mul]

-- finRange
def myFinRange (n : Nat) : List (Fin n) := ofFn id

theorem finRange_succ {n} : finRange (n+1) = 0 :: (finRange n).map Fin.succ := by
  apply List.ext_getElem
  · simp
  · intro i
    cases i <;> simp

theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
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

open List
variable (n : ℕ) (α : Type) (x : (Fin n) → α)

example (σ : Equiv.Perm (Fin n)) :
    (finRange n).map (x ∘ σ) ~ (finRange n).map x := by
  rw [← map_map]
  apply Perm.map
  exact Equiv.Perm.map_finRange_perm σ

/-- Define a monoid structure on ℕ using addition. -/
Statement (m n : ℕ) :
    ((range m).map x).prod * ((range n).map (fun v => x (m + v))).prod =
    ((range (m+n)).map x).prod := by
  induction n
  · simp
  · rw [prod_range_succ, ← mul_assoc (map x (range m)).prod, a, ←prod_range_succ]
    simp [Nat.add_assoc]

Conclusion "This last message appears if the level is solved."
