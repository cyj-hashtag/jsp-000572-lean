import Problem572.Reduction

/-!
# The singleton-intersection theorem

The threshold is explicit but is not optimized. The proof follows Frankl's
kernel and deletion argument; the block-counting step is replaced by a
minimum-degree argument using the Erdos-Ko-Rado theorem.
-/

namespace Problem572

open Finset

def theoremThreshold (k : ℕ) : ℕ :=
  localThreshold k + 2 * (localThreshold k).choose k + 1

theorem singleton_free_bound {α : Type*} [DecidableEq α] {k : ℕ}
    (hk : 4 ≤ k) (X : Finset α) (F : Finset (Finset α))
    (hX : Supported X F) (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (hn : theoremThreshold k ≤ X.card) :
    F.card ≤ (X.card - 2).choose (k - 2) := by
  exact card_le_of_localReduction (local_reduction hk) X F hX hU hF
    (by unfold theoremThreshold at hn; omega)

theorem singleton_intersection {α : Type*} [DecidableEq α] {k : ℕ}
    (hk : 4 ≤ k) (X : Finset α) (F : Finset (Finset α))
    (hX : Supported X F) (hU : Uniform k F)
    (hn : theoremThreshold k ≤ X.card)
    (hlarge : (X.card - 2).choose (k - 2) < F.card) :
    ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ (A ∩ B).card = 1 := by
  exact exists_intersection_of_localReduction (local_reduction hk) hk X F hX hU
    (by unfold theoremThreshold at hn; omega) hlarge

theorem erdos_sos_singleton_intersection :
    ∀ k : ℕ, 4 ≤ k →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ F : Finset (Finset (Fin n)),
          (∀ A ∈ F, A.card = k) →
          Nat.choose (n - 2) (k - 2) < F.card →
          ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ (A ∩ B).card = 1 := by
  intro k hk
  refine ⟨theoremThreshold k, ?_⟩
  intro n hn F hU hlarge
  apply singleton_intersection hk (univ : Finset (Fin n)) F
    (fun _ _ => subset_univ _) hU
  · simpa using hn
  · simpa using hlarge

theorem fixed_pair_sharpness {α : Type*} [DecidableEq α] {k : ℕ} {X : Finset α}
    (hk : 2 ≤ k) (hn : k ≤ X.card) :
    ∃ F : Finset (Finset α), Uniform k F ∧ Supported X F ∧
      NoSingletonIntersections F ∧ F.card = (X.card - 2).choose (k - 2) := by
  obtain ⟨P, hPX, hPc⟩ := exists_subset_card_eq (hk.trans hn)
  let F := containing (X.powersetCard k) P
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact (mem_powersetCard.mp (mem_containing.mp hA).1).2
  · intro A hA
    exact (mem_powersetCard.mp (mem_containing.mp hA).1).1
  · intro A hA B hB he
    have hPA := (mem_containing.mp hA).2
    have hPB := (mem_containing.mp hB).2
    have hh := card_le_card (subset_inter hPA hPB)
    omega
  · simpa only [hPc] using fixed_core_count hPX (by omega : P.card ≤ k)

end Problem572
