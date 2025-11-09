import Game.Metadata
-- import Mathlib.Data.Multiset.Basic
-- import Mathlib.Data.Multiset.Defs

import Mathlib.Data.Finset.Sigma
-- import Mathlib.Data.Finset.Prod

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

import Mathlib.Data.Multiset.MapFold

open Multiset

-- Subtype is a type that contain a proof of a proposiotion of that type
example (α : Type) (x : α) (s : Multiset α) (hx : x ∈ s) : {x // x ∈ s} := by
  exact ⟨x, hx⟩

variable {α β : Type*} {s : Multiset α} {t : Multiset β}
  (hs : s.Nodup)
  (ht : t.Nodup)
  (i : ∀ a ∈ s, β)
  (hi : ∀ a ha, i a ha ∈ t)
  (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b)
  (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)

example (b : β) : b ∈ t → ∃ a ∈ s.attach, i a.1 a.2 = b := by
  intro hb
  rcases i_surj b hb with ⟨a, ha, rfl⟩
  -- we can use rcases to split the surjectiion hypothesis and rewrite the goal
  -- at the same time
  -- notice that rfl makes the substitiion in the goal, : β rewriting the goal in our favour.
  exact ⟨⟨a, ha⟩, mem_attach _ _, rfl⟩
  -- we can close the goal by using nested `⟨⟩` syntax to construct a term that
  -- closes the goal.
  -- specifically, we need to provide a term of type ?x ∈ s.attach. `mem_attach` fits
  -- this but it requires two argument. Notice that we can let lean figure out the
  -- by placing `_` holes

example : t = s.attach.map (fun x => i x.1 x.2) := by
  rw [ht.ext]
  · simp only [mem_map]
    intro b
    constructor
    · intro hb
      rcases i_surj b hb with ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, mem_attach _ _, rfl⟩
    · rintro ⟨_, ⟨_, rfl⟩⟩
      exact hi w.1 w.2
  · apply Multiset.Nodup.map
    · unfold Function.Injective
      simpa using i_inj
    · exact hs.attach

variable (f : α → γ) (g : β → γ)

example (h : ∀ a ha, f a = g (i a ha)) : s.map f = t.map g := by
  have : t = s.attach.map fun x => i x.1 x.2 := by sorry
  rw [←pmap_eq_map _ _ _ (fun _ => id), pmap_eq_map_attach, this, map_map]
  exact map_congr rfl fun x _ => h _ _
