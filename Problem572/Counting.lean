import Problem572.Basic

namespace Problem572

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
theorem card_le_sum_of_cover (F : Finset α) (T : Finset β) (G : β → Finset α)
    (h : ∀ A ∈ F, ∃ B ∈ T, A ∈ G B) :
    F.card ≤ ∑ B ∈ T, (G B).card := by
  calc
    F.card ≤ (T.biUnion G).card := card_le_card (by
      intro A hA
      obtain ⟨B, hB, hAB⟩ := h A hA
      exact mem_biUnion.mpr ⟨B, hB, hAB⟩)
    _ ≤ ∑ B ∈ T, (G B).card := card_biUnion_le

omit [DecidableEq β] in
theorem containing_card_le {k : ℕ} {X B : Finset α} {F : Finset (Finset α)}
    (hU : Uniform k F) (hX : Supported X F) (hB : B ⊆ X) :
    (containing F B).card ≤ (X.card - B.card).choose (k - B.card) := by
  rw [← card_sdiff hB, ← card_powersetCard]
  apply card_le_card_of_injOn (fun A => A \ B)
  · intro A hA
    obtain ⟨hA, hBA⟩ := mem_containing.mp hA
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff (hX A hA) Subset.rfl,
      by rw [card_sdiff hBA, hU A hA]⟩
  · intro A hA C hC he
    have hBA := (mem_containing.mp hA).2
    have hBC := (mem_containing.mp hC).2
    have := congrArg (fun S => S ∪ B) he
    simpa [sdiff_union_of_subset hBA, sdiff_union_of_subset hBC] using this

omit [DecidableEq β] in
theorem containing_card_le_pow {k : ℕ} {X B : Finset α} {F : Finset (Finset α)}
    (hU : Uniform k F) (hX : Supported X F) :
    (containing F B).card ≤ X.card ^ (k - B.card) := by
  by_cases hB : B ⊆ X
  · exact (containing_card_le hU hX hB).trans
      ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
  · have he : containing F B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨hA, hBA⟩ := mem_containing.mp hA
      exact hB (hBA.trans (hX A hA))
    simp [he]

omit [DecidableEq β] in
theorem fixed_core_count {k : ℕ} {X B : Finset α}
    (hB : B ⊆ X) (hk : B.card ≤ k) :
    (containing (X.powersetCard k) B).card =
      (X.card - B.card).choose (k - B.card) := by
  rw [← card_sdiff hB, ← card_powersetCard]
  apply card_bij (fun A _ => A \ B)
  · intro A hA
    obtain ⟨hA, hBA⟩ := mem_containing.mp hA
    obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp hA
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff hAX Subset.rfl,
      by rw [card_sdiff hBA, hAk]⟩
  · intro A hA C hC he
    have hBA := (mem_containing.mp hA).2
    have hBC := (mem_containing.mp hC).2
    have := congrArg (fun S => S ∪ B) he
    simpa [sdiff_union_of_subset hBA, sdiff_union_of_subset hBC] using this
  · intro A hA
    obtain ⟨hAX, hAk⟩ := mem_powersetCard.mp hA
    have hd : Disjoint A B := disjoint_left.mpr (fun a ha => (mem_sdiff.mp (hAX ha)).2)
    refine ⟨A ∪ B, mem_containing.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩,
      subset_union_right⟩, ?_⟩
    · exact union_subset (hAX.trans sdiff_subset) hB
    · rw [card_union_of_disjoint hd, hAk, Nat.sub_add_cancel hk]
    · exact union_sdiff_cancel_right hd

end Problem572
