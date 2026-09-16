import Problem572.Kernels

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

theorem rich_extension_outside {k : ℕ} {F : Finset (Finset α)} {X T H : Finset α}
    (hk : 4 ≤ k) (hU : Uniform k F) (hX : Supported X F)
    (hTX : T ⊆ X) (hTc : T.card = 3)
    (hlarge : (H.card + k) * X.card ^ (k - 4) < (containing F T).card) :
    ∃ z ∈ X, z ∉ T ∧ z ∉ H ∧ Rich k F (insert z T) := by
  classical
  let good := (containing F T).filter (fun A => Disjoint (A \ T) H)
  let bad := (containing F T).filter (fun A => ¬Disjoint (A \ T) H)
  have hsplit : good.card + bad.card = (containing F T).card :=
    filter_card_add_filter_neg_card_eq_card _
  have hbad : bad.card ≤ H.card * X.card ^ (k - 4) := by
    let D := H \ T
    calc
      bad.card ≤ ∑ z ∈ D, (containing F (insert z T)).card :=
        card_le_sum_of_cover _ _ _ (by
          intro A hA
          obtain ⟨hA, hn⟩ := mem_filter.mp hA
          obtain ⟨hA, hTA⟩ := mem_containing.mp hA
          obtain ⟨z, hzA, hzH⟩ := not_disjoint_iff.mp hn
          obtain ⟨hzA, hzT⟩ := mem_sdiff.mp hzA
          exact ⟨z, mem_sdiff.mpr ⟨hzH, hzT⟩,
            mem_containing.mpr ⟨hA, insert_subset hzA hTA⟩⟩)
      _ ≤ ∑ _z ∈ D, X.card ^ (k - 4) := by
        apply sum_le_sum
        intro z hz
        have hzT := (mem_sdiff.mp hz).2
        simpa [card_insert_of_notMem hzT, hTc] using
          (containing_card_le_pow (B := insert z T) hU hX)
      _ = D.card * X.card ^ (k - 4) := by simp
      _ ≤ H.card * X.card ^ (k - 4) :=
        Nat.mul_le_mul_right _ (card_le_card sdiff_subset)
  have hgood : k * X.card ^ (k - 4) < good.card := by
    rw [Nat.add_mul] at hlarge
    omega
  by_contra hn
  push_neg at hn
  by_cases hk4 : k = 4
  · obtain ⟨A, hA⟩ := card_pos.mp (by omega : 0 < good.card)
    obtain ⟨hA, hd⟩ := mem_filter.mp hA
    obtain ⟨hA, hTA⟩ := mem_containing.mp hA
    have hAc := hU A hA
    have hdiff : (A \ T).Nonempty := by
      rw [← card_pos, card_sdiff hTA, hAc, hk4, hTc]
      decide
    obtain ⟨z, hz⟩ := hdiff
    obtain ⟨hzA, hzT⟩ := mem_sdiff.mp hz
    have hzH : z ∉ H := fun hzH => disjoint_left.mp hd (mem_sdiff.mpr ⟨hzA, hzT⟩) hzH
    have hQ : insert z T = A := eq_of_subset_of_card_le (insert_subset hzA hTA)
      (by rw [card_insert_of_notMem hzT, hTc, hAc, hk4])
    exact hn z (hX A hA hzA) hzT hzH (Rich.of_mem (hQ.symm ▸ hA))
  · have hk5 : 5 ≤ k := by omega
    let Z := (X \ T) \ H
    have hgoodBound : good.card ≤ X.card * (k * X.card ^ (k - 5)) := by
      calc
        good.card ≤ ∑ z ∈ Z, (containing F (insert z T)).card :=
          card_le_sum_of_cover _ _ _ (by
            intro A hA
            obtain ⟨hA, hd⟩ := mem_filter.mp hA
            obtain ⟨hA, hTA⟩ := mem_containing.mp hA
            have hdiff : (A \ T).Nonempty := by
              rw [← card_pos, card_sdiff hTA, hU A hA, hTc]
              omega
            obtain ⟨z, hz⟩ := hdiff
            obtain ⟨hzA, hzT⟩ := mem_sdiff.mp hz
            have hzH : z ∉ H := fun hzH => disjoint_left.mp hd (mem_sdiff.mpr ⟨hzA, hzT⟩) hzH
            exact ⟨z, mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hX A hA hzA, hzT⟩, hzH⟩,
              mem_containing.mpr ⟨hA, insert_subset hzA hTA⟩⟩)
        _ ≤ ∑ _z ∈ Z, k * X.card ^ (k - 5) := by
          apply sum_le_sum
          intro z hz
          obtain ⟨hzXT, hzH⟩ := mem_sdiff.mp hz
          obtain ⟨hzX, hzT⟩ := mem_sdiff.mp hzXT
          have hQ := nonrich_count (hn z hzX hzT hzH) hU hX (insert_subset hzX hTX)
          have hQc : (insert z T).card = 4 := by rw [card_insert_of_notMem hzT, hTc]
          rw [hQc] at hQ
          calc
            (containing F (insert z T)).card ≤ k * (X.card - 5).choose (k - 5) := hQ
            _ ≤ k * X.card ^ (k - 5) := Nat.mul_le_mul_left _
              ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
        _ = Z.card * (k * X.card ^ (k - 5)) := by simp
        _ ≤ X.card * (k * X.card ^ (k - 5)) := Nat.mul_le_mul_right _
          (card_le_card (sdiff_subset.trans sdiff_subset))
    have he : X.card * (k * X.card ^ (k - 5)) = k * X.card ^ (k - 4) := by
      have he : k - 4 = (k - 5) + 1 := by omega
      rw [he, pow_succ]
      ring
    rw [he] at hgoodBound
    omega

end Problem572
