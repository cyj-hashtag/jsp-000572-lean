import Problem572.Kernels

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def pairKernels (k : ℕ) (X : Finset α) (F : Finset (Finset α)) :
    Finset (Finset α) := by
  classical
  exact (X.powersetCard 2).filter (Rich k F)

omit [DecidableEq α] in
@[simp] theorem mem_pairKernels {k : ℕ} {X P : Finset α} {F : Finset (Finset α)} :
    P ∈ pairKernels k X F ↔ P ⊆ X ∧ P.card = 2 ∧ Rich k F P := by
  classical
  simp [pairKernels, and_assoc]

theorem pair_kernel_all_or_none {k : ℕ} {F : Finset (Finset α)} {P A : Finset α}
    (hP : Rich k F P) (hc : P.card = 2) (hU : Uniform k F)
    (hF : NoSingletonIntersections F) (hA : A ∈ F) :
    Disjoint P A ∨ P ⊆ A := by
  have hn := hP.inter_member_ne_one hU hF hA
  have hle : (P ∩ A).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hc
  by_cases h0 : (P ∩ A).card = 0
  · exact Or.inl (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp h0))
  · right
    have he : (P ∩ A).card = P.card := by omega
    have hs : P ∩ A = P := eq_of_subset_of_card_le inter_subset_left (by omega)
    exact inter_eq_left.mp hs

theorem pair_kernels_disjoint {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    (hU : Uniform k F) (hF : NoSingletonIntersections F) :
    ∀ P ∈ pairKernels k X F, ∀ Q ∈ pairKernels k X F,
      P ≠ Q → Disjoint P Q := by
  intro P hP Q hQ hne
  obtain ⟨_, hPc, hPr⟩ := mem_pairKernels.mp hP
  obtain ⟨_, hQc, hQr⟩ := mem_pairKernels.mp hQ
  have hn := hPr.inter_ne_one hQr hU hF
  have hle : (P ∩ Q).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hPc
  apply disjoint_iff_inter_eq_empty.mpr
  apply card_eq_zero.mp
  by_contra hh
  have he : (P ∩ Q).card = 2 := by omega
  have h1 : P ∩ Q = P := eq_of_subset_of_card_le inter_subset_left (by omega)
  have h2 : P ∩ Q = Q := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hne (h1.symm.trans h2)

theorem rich_triple_contains_pair {k : ℕ} {F : Finset (Finset α)} {T : Finset α}
    (hTc : T.card = 3) (hT : Rich k F T) (hU : Uniform k F)
    (hF : NoSingletonIntersections F)
    (hp : ∃ P, P ⊆ T ∧ P.card = 2 ∧ Rich k F P) :
    ∃ P, P ⊆ T ∧ P.card = 2 ∧ Rich k F P ∧
      ∀ A ∈ F, (T ∩ A).Nonempty → P ⊆ A := by
  obtain ⟨P, hPT, hPc, hPr⟩ := hp
  refine ⟨P, hPT, hPc, hPr, ?_⟩
  intro A hA hm
  rcases pair_kernel_all_or_none hPr hPc hU hF hA with hd | hs
  · exfalso
    have hsub : T ∩ A ⊆ T \ P := by
      intro a ha
      obtain ⟨haT, haA⟩ := mem_inter.mp ha
      exact mem_sdiff.mpr ⟨haT, fun haP => disjoint_left.mp hd haP haA⟩
    have hc := card_le_card hsub
    rw [card_sdiff hPT, hTc, hPc] at hc
    have hpos := card_pos.mpr hm
    exact hT.inter_member_ne_one hU hF hA (by omega)
  · exact hs

theorem high_degree_has_rich_triple {r k : ℕ} {F : Finset (Finset α)}
    {X : Finset α} {x : α} (hx : x ∈ X)
    (hX : Supported X F) (hU : Uniform k F)
    (hn : ∀ D, x ∈ D → D.card < 3 → ¬Rich r F D)
    (hc : r ^ 3 * (X.card - 4).choose (k - 4) < (link F x).card) :
    ∃ T, x ∈ T ∧ T.card = 3 ∧ Rich r F T := by
  by_contra! ht
  have hnon : ∀ D, ({x} : Finset α) ⊆ D → D.card < ({x} : Finset α).card + 3 →
      ¬Rich r F D := by
    intro D hD hDc
    have hxD := hD (mem_singleton_self x)
    have hDc' : D.card < 4 := by simpa using hDc
    by_cases h3 : D.card < 3
    · exact hn D hxD h3
    · exact ht D hxD (by omega)
  obtain ⟨C, hC, hCs, hcover, _⟩ := uniform_extension_cover r 3 hX
    (singleton_subset_iff.mpr hx) hnon
  have hcount : (containing F {x}).card ≤ r ^ 3 * (X.card - 4).choose (k - 4) := by
    calc
      (containing F {x}).card ≤ ∑ D ∈ C, (containing F D).card :=
        card_le_sum_of_cover _ _ _ (by
          intro A hA
          obtain ⟨hA, hxA⟩ := mem_containing.mp hA
          obtain ⟨D, hD, hDA⟩ := hcover A hA hxA
          exact ⟨D, hD, mem_containing.mpr ⟨hA, hDA⟩⟩)
      _ ≤ ∑ _D ∈ C, (X.card - 4).choose (k - 4) := by
        apply sum_le_sum
        intro D hD
        obtain ⟨_, hDX, hDc⟩ := hCs D hD
        have hDc' : D.card = 4 := by simpa using hDc
        simpa [hDc'] using containing_card_le hU hX hDX
      _ = C.card * (X.card - 4).choose (k - 4) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hC
  have hlink : (link F x).card = (containing F {x}).card := by
    rw [card_link]
    simp [containing, singleton_subset_iff]
  rw [hlink] at hc
  omega

end Problem572
