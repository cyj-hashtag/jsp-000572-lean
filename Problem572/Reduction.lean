import Problem572.Blocks
import Problem572.Descent

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def localThreshold (k : ℕ) : ℕ :=
  max (2 * k) (max (growthThreshold (rigidityConstant k) (k - 4))
    (growthThreshold 1 (k - 4)))

theorem extremalBound_step {k n : ℕ} (hk : 3 ≤ k) (hn : 3 ≤ n) :
    extremalBound k n = extremalBound k (n - 1) + (n - 3).choose (k - 3) := by
  unfold extremalBound
  have hs1 : (n - 3) + 1 = n - 2 := by omega
  have hs2 : (k - 3) + 1 = k - 2 := by omega
  have hh := Nat.choose_succ_succ (n - 3) (k - 3)
  simpa only [Nat.succ_eq_add_one, hs1, hs2, Nat.sub_sub, Nat.add_comm] using hh

theorem degree_deletion {k : ℕ} {X : Finset α} {F : Finset (Finset α)} {x : α}
    (hk : 4 ≤ k) (hn : 4 ≤ X.card) (hx : x ∈ X) (hX : Supported X F)
    (he : extremalBound k X.card < F.card)
    (hd : (link F x).card < (X.card - 3).choose (k - 3)) :
    ∃ Y : Finset α, Y ⊆ X ∧ Y.card < X.card ∧ X.card ≤ Y.card + 2 ∧
      excess k X F + 1 ≤ excess k Y (restrict F Y) := by
  have hc : (X.erase x).card = X.card - 1 := card_erase_of_mem hx
  have hrestrict : restrict F (X.erase x) = F.filter (fun A => x ∉ A) := by
    ext A
    simp only [mem_restrict, mem_filter]
    constructor
    · rintro ⟨hA, hAS⟩
      exact ⟨hA, fun hxA => notMem_erase x X (hAS hxA)⟩
    · rintro ⟨hA, hxA⟩
      exact ⟨hA, fun y hy => mem_erase.mpr ⟨by rintro rfl; exact hxA hy, hX A hA hy⟩⟩
  have hsplit : (link F x).card + (restrict F (X.erase x)).card = F.card := by
    rw [card_link, hrestrict]
    exact filter_card_add_filter_neg_card_eq_card _
  have hstep := extremalBound_step (by omega : 3 ≤ k) (by omega : 3 ≤ X.card)
  refine ⟨X.erase x, erase_subset _ _, by omega, by omega, ?_⟩
  unfold excess
  rw [hc]
  omega

theorem pair_deletion {k : ℕ} {X : Finset α} {F : Finset (Finset α)} {x y : α}
    (hk : 4 ≤ k) (hn : k + 1 ≤ X.card) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hX : Supported X F) (he : extremalBound k X.card < F.card)
    (hd : (F.filter (fun A => x ∈ A ∨ y ∈ A)).card ≤ (X.card - 3).choose (k - 3)) :
    ∃ Y : Finset α, Y ⊆ X ∧ Y.card < X.card ∧ X.card ≤ Y.card + 2 ∧
      excess k X F + 1 ≤ excess k Y (restrict F Y) := by
  have hy' : y ∈ X.erase x := mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hc : ((X.erase x).erase y).card = X.card - 2 := by
    rw [card_erase_of_mem hy', card_erase_of_mem hx, Nat.sub_sub]
  let Y := (X.erase x).erase y
  have hrestrict : restrict F Y = F.filter (fun A => ¬(x ∈ A ∨ y ∈ A)) := by
    ext A
    simp only [mem_restrict, mem_filter]
    constructor
    · rintro ⟨hA, hAS⟩
      refine ⟨hA, ?_⟩
      rintro (hxA | hyA)
      · exact notMem_erase x X (mem_erase.mp (hAS hxA)).2
      · exact notMem_erase y (X.erase x) (hAS hyA)
    · rintro ⟨hA, hnA⟩
      refine ⟨hA, ?_⟩
      intro z hz
      apply mem_erase.mpr
      refine ⟨?_, mem_erase.mpr ⟨?_, hX A hA hz⟩⟩
      · rintro rfl
        exact hnA (Or.inr hz)
      · rintro rfl
        exact hnA (Or.inl hz)
  have hsplit : (F.filter (fun A => x ∈ A ∨ y ∈ A)).card + (restrict F Y).card = F.card := by
    rw [hrestrict]
    exact filter_card_add_filter_neg_card_eq_card _
  have hstep1 := extremalBound_step (by omega : 3 ≤ k) (by omega : 3 ≤ X.card)
  have hstep2 := extremalBound_step (by omega : 3 ≤ k) (by omega : 3 ≤ X.card - 1)
  have hpos : 0 < (X.card - 4).choose (k - 3) := Nat.choose_pos (by omega)
  norm_num only [Nat.sub_sub] at hstep2
  refine ⟨Y, (erase_subset _ _).trans (erase_subset _ _), by dsimp [Y]; omega,
    by dsimp [Y]; omega, ?_⟩
  unfold excess
  have hc' : Y.card = X.card - 2 := hc
  rw [hc']
  omega

theorem local_reduction {k : ℕ} (hk : 4 ≤ k) : LocalReduction k (localThreshold k) α := by
  classical
  intro X F hX hU hF hn he
  have hthreshold : localThreshold k ≤ X.card := Nat.le_of_lt hn
  have h2k : 2 * k ≤ X.card := (le_max_left _ _).trans hthreshold
  have hgR : growthThreshold (rigidityConstant k) (k - 4) ≤ X.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold)
  have hg1 : growthThreshold 1 (k - 4) ≤ X.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hthreshold)
  by_cases hlow : ∃ x ∈ X, (link F x).card < (X.card - 3).choose (k - 3)
  · obtain ⟨x, hx, hd⟩ := hlow
    exact degree_deletion hk (by omega) hx hX he hd
  · push_neg at hlow
    have hdeg : ∀ x ∈ X, rigidityConstant k * X.card ^ (k - 4) < (link F x).card := by
      intro x hx
      have hh := pow_lt_half_choose (rigidityConstant k) (k - 4) X.card hgR
      have hs : k - 4 + 1 = k - 3 := by omega
      rw [hs] at hh
      exact hh.trans_le ((Nat.choose_le_choose _ (by omega : X.card / 2 - 3 ≤ X.card - 3)).trans (hlow x hx))
    rcases high_degree_structure hk hU hX hF hdeg with hpair | hstruct
    · obtain ⟨x, hx, y, hy, hxy, hd⟩ := hpair
      exact pair_deletion hk (by omega) hx hy hxy hX he hd
    · have hchoose : ∀ x, ∃ P : Finset α, x ∈ X → P.card = 2 ∧ Rich k F P ∧
          ∀ A ∈ F, x ∈ A → P ⊆ A := by
        intro x
        by_cases hx : x ∈ X
        · obtain ⟨P, hP⟩ := hstruct x hx
          exact ⟨P, fun _ => hP⟩
        · exact ⟨∅, fun hh => (hx hh).elim⟩
      choose p hp using hchoose
      rcases structured_low_degree_or_bound hk h2k hg1 hp hU hX hF with hbound | hpoint
      · exact (not_lt_of_ge hbound he).elim
      · obtain ⟨x, hx, hd⟩ := hpoint
        exact degree_deletion hk (by omega) hx hX he hd

end Problem572
