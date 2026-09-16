import Problem572.Rigidity
import Problem572.IntersectingBound
import Problem572.Numerics

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def PairAssignment (k : ℕ) (X : Finset α) (F : Finset (Finset α))
    (p : α → Finset α) : Prop :=
  ∀ x ∈ X, (p x).card = 2 ∧ Rich k F (p x) ∧ ∀ A ∈ F, x ∈ A → p x ⊆ A

noncomputable def block (X : Finset α) (p : α → Finset α) (P : Finset α) : Finset α := by
  classical
  exact X.filter (fun x => p x = P)

@[simp] theorem mem_block {X P : Finset α} {p : α → Finset α} {x : α} :
    x ∈ block X p P ↔ x ∈ X ∧ p x = P := by
  classical
  simp [block]

theorem PairAssignment.core {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} (hp : PairAssignment k X F p) {P : Finset α}
    (hP : P ∈ X.image p) : P.card = 2 ∧ Rich k F P := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hP
  exact ⟨(hp x hx).1, (hp x hx).2.1⟩

theorem PairAssignment.fixed {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} (hp : PairAssignment k X F p) (hk : 2 ≤ k)
    (hX : Supported X F) {P : Finset α} (hPc : P.card = 2) (hP : Rich k F P)
    {x : α} (hx : x ∈ P) : p x = P := by
  have hxX := hP.subset_support hX hx
  obtain ⟨hpc, _, hforce⟩ := hp x hxX
  exact eq_of_subset_of_card_le (hP.forced_subset hx (by omega) hforce) (by omega)

theorem PairAssignment.core_subset_block {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} (hp : PairAssignment k X F p) (hk : 2 ≤ k)
    (hX : Supported X F) {P : Finset α} (hP : P ∈ X.image p) : P ⊆ block X p P := by
  obtain ⟨hPc, hPr⟩ := hp.core hP
  intro x hx
  exact mem_block.mpr ⟨hPr.subset_support hX hx, hp.fixed hk hX hPc hPr hx⟩

theorem PairAssignment.cores_disjoint {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} (hp : PairAssignment k X F p) (hU : Uniform k F)
    (hX : Supported X F) (hF : NoSingletonIntersections F)
    {P Q : Finset α} (hP : P ∈ X.image p) (hQ : Q ∈ X.image p) (hne : P ≠ Q) :
    Disjoint P Q := by
  obtain ⟨hPc, hPr⟩ := hp.core hP
  obtain ⟨hQc, hQr⟩ := hp.core hQ
  exact pair_kernels_disjoint hU hF P
    (mem_pairKernels.mpr ⟨hPr.subset_support hX, hPc, hPr⟩) Q
    (mem_pairKernels.mpr ⟨hQr.subset_support hX, hQc, hQr⟩) hne

theorem pair_only_block_low_degree {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} {P : Finset α}
    (hk : 4 ≤ k) (hn : 2 * k ≤ X.card)
    (hp : PairAssignment k X F p) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F) (hP : P ∈ X.image p) (hS : block X p P = P) :
    ∃ x ∈ X, (link F x).card < (X.card - 3).choose (k - 3) := by
  classical
  obtain ⟨hPc, hPr⟩ := hp.core hP
  have hPX := hPr.subset_support hX
  let G := (containing F P).image (fun A => A \ P)
  have hGc : G.card = (containing F P).card := by
    apply card_image_iff.mpr
    intro A hA B hB he
    have hPA := (mem_containing.mp hA).2
    have hPB := (mem_containing.mp hB).2
    simpa [sdiff_union_of_subset hPA, sdiff_union_of_subset hPB] using
      congrArg (fun S => S ∪ P) he
  have hGU : Uniform (k - 2) G := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    obtain ⟨hB, hPB⟩ := mem_containing.mp hB
    rw [card_sdiff hPB, hU B hB, hPc]
  have hGX : Supported (X \ P) G := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact sdiff_subset_sdiff (hX B (mem_containing.mp hB).1) Subset.rfl
  have hGF : NoSingletonIntersections G := by
    intro A hA B hB hc
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hA
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
    obtain ⟨hC, hPC⟩ := mem_containing.mp hC
    obtain ⟨hD, hPD⟩ := mem_containing.mp hD
    obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < ((C \ P) ∩ (D \ P)).card)
    obtain ⟨hyC, hyD⟩ := mem_inter.mp hy
    obtain ⟨hyC, hyP⟩ := mem_sdiff.mp hyC
    have hyX := hX C hC hyC
    have hyD' := (mem_sdiff.mp hyD).1
    obtain ⟨hQc, _, hforce⟩ := hp y hyX
    have hne : p y ≠ P := by
      intro he
      have hyS := mem_block.mpr ⟨hyX, he⟩
      rw [hS] at hyS
      exact hyP hyS
    have hd := hp.cores_disjoint hU hX hF (mem_image_of_mem p hyX) hP hne
    have hsub : p y ⊆ (C \ P) ∩ (D \ P) := by
      intro z hz
      have hzP : z ∉ P := fun hzP => disjoint_left.mp hd hz hzP
      exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨hforce C hC hyC hz, hzP⟩,
        mem_sdiff.mpr ⟨hforce D hD hyD' hz, hzP⟩⟩
    have hh := card_le_card hsub
    omega
  have hnc : (X \ P).card = X.card - 2 := by rw [card_sdiff hPX, hPc]
  have hg := singleton_free_card_bound hGU hGX hGF (by rw [hnc]; omega)
  have hg' : G.card * (k - 2) ≤ (X.card - 2) * (X.card - 4).choose (k - 4) := by
    simpa only [hnc, Nat.sub_sub] using hg
  have hsmall := pair_residual_degree_lt hk (by omega : k < X.card) hg'
  obtain ⟨x, hxP⟩ := card_pos.mp (by omega : 0 < P.card)
  have hxX := hPX hxP
  have hpx := hp.fixed (by omega) hX hPc hPr hxP
  have he : F.filter (x ∈ ·) = containing F P := by
    ext A
    simp only [mem_filter, mem_containing]
    exact ⟨fun ⟨hA, hxA⟩ => ⟨hA, hpx ▸ (hp x hxX).2.2 A hA hxA⟩,
      fun ⟨hA, hPA⟩ => ⟨hA, hPA hxP⟩⟩
  refine ⟨x, hxX, ?_⟩
  simpa only [card_link, he, hGc] using hsmall

theorem satellite_degree_bound {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} {P : Finset α} {x : α}
    (hk : 4 ≤ k) (hp : PairAssignment k X F p) (hU : Uniform k F)
    (hX : Supported X F) (hF : NoSingletonIntersections F)
    (hP : P ∈ X.image p) (hxS : x ∈ block X p P) (hxP : x ∉ P) :
    (link F x).card ≤ ((block X p P).card - 3).choose (k - 3) + X.card ^ (k - 4) := by
  classical
  let S := block X p P
  let I := (containing F {x}).filter (· ⊆ S)
  let E := (containing F {x}).filter (fun A => ¬A ⊆ S)
  let D := (X.image p).filter (· ≠ P)
  obtain ⟨hxX, hpx⟩ := mem_block.mp hxS
  obtain ⟨hPc, hPr⟩ := hp.core hP
  have hPS := hp.core_subset_block (by omega) hX hP
  have hcore : (insert x P).card = 3 := by rw [card_insert_of_notMem hxP, hPc]
  have hforce : ∀ A ∈ F, x ∈ A → P ⊆ A := by
    intro A hA hxA
    simpa only [hpx] using (hp x hxX).2.2 A hA hxA
  have hinside : I.card ≤ (S.card - 3).choose (k - 3) := by
    calc
      I.card ≤ (containing (restrict F S) (insert x P)).card := card_le_card (by
        intro A hA
        obtain ⟨hA, hAS⟩ := mem_filter.mp hA
        obtain ⟨hA, hxA⟩ := mem_containing.mp hA
        have hxA' := hxA (mem_singleton_self x)
        exact mem_containing.mpr ⟨mem_restrict.mpr ⟨hA, hAS⟩,
          insert_subset hxA' (hforce A hA hxA')⟩)
      _ ≤ _ := by
        have hh := containing_card_le (hU.mono (filter_subset _ _))
          (show Supported S (restrict F S) from fun A hA => (mem_restrict.mp hA).2)
          (insert_subset hxS hPS)
        simpa only [hcore] using hh
  have hDcore : ∀ Q ∈ D, (insert x (P ∪ Q)).card = 5 := by
    intro Q hQ
    obtain ⟨hQ, hQP⟩ := mem_filter.mp hQ
    obtain ⟨hQc, hQr⟩ := hp.core hQ
    have hd := hp.cores_disjoint hU hX hF hP hQ (Ne.symm hQP)
    have hxQ : x ∉ Q := by
      intro hxQ
      exact hQP ((hp.fixed (by omega) hX hQc hQr hxQ).symm.trans hpx)
    rw [card_insert_of_notMem (by simpa using And.intro hxP hxQ),
      card_union_of_disjoint hd, hPc, hQc]
  have hcover : ∀ A ∈ E, ∃ Q ∈ D, insert x (P ∪ Q) ⊆ A := by
    intro A hA
    obtain ⟨hA, hnS⟩ := mem_filter.mp hA
    obtain ⟨hA, hxA⟩ := mem_containing.mp hA
    have hxA' := hxA (mem_singleton_self x)
    obtain ⟨y, hyA, hyS⟩ := not_subset.mp hnS
    have hyX := hX A hA hyA
    have hne : p y ≠ P := fun he => hyS (mem_block.mpr ⟨hyX, he⟩)
    exact ⟨p y, mem_filter.mpr ⟨mem_image_of_mem p hyX, hne⟩,
      insert_subset hxA' (union_subset (hforce A hA hxA') ((hp y hyX).2.2 A hA hyA))⟩
  have hcross : E.card ≤ X.card ^ (k - 4) := by
    by_cases hk4 : k = 4
    · have he : E = ∅ := eq_empty_iff_forall_notMem.mpr (by
        intro A hA
        obtain ⟨Q, hQ, hQA⟩ := hcover A hA
        have hAc := hU A (mem_containing.mp (mem_filter.mp hA).1).1
        have hh := card_le_card hQA
        rw [hDcore Q hQ, hAc, hk4] at hh
        omega)
      simp [he]
    · have hk5 : 5 ≤ k := by omega
      calc
        E.card ≤ ∑ Q ∈ D, (containing F (insert x (P ∪ Q))).card :=
          card_le_sum_of_cover _ _ _ (by
            intro A hA
            obtain ⟨Q, hQ, hQA⟩ := hcover A hA
            exact ⟨Q, hQ, mem_containing.mpr
              ⟨(mem_containing.mp (mem_filter.mp hA).1).1, hQA⟩⟩)
        _ ≤ ∑ _Q ∈ D, X.card ^ (k - 5) := by
          apply sum_le_sum
          intro Q hQ
          simpa only [hDcore Q hQ] using
            (containing_card_le_pow (B := insert x (P ∪ Q)) hU hX)
        _ = D.card * X.card ^ (k - 5) := by simp
        _ ≤ X.card * X.card ^ (k - 5) := Nat.mul_le_mul_right _
          ((card_le_card (filter_subset _ _)).trans card_image_le)
        _ = X.card ^ (k - 4) := by
          rw [show k - 4 = (k - 5) + 1 by omega, pow_succ]
          exact Nat.mul_comm _ _
  have hsplit : I.card + E.card = (containing F {x}).card :=
    filter_card_add_filter_neg_card_eq_card _
  have hlink : (link F x).card = (containing F {x}).card := by
    rw [card_link]
    simp [containing, singleton_subset_iff]
  rw [hlink, ← hsplit]
  exact Nat.add_le_add hinside hcross

theorem small_block_low_degree {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α} {P : Finset α}
    (hk : 4 ≤ k) (hn : 2 * k ≤ X.card)
    (hg : growthThreshold 1 (k - 4) ≤ X.card)
    (hp : PairAssignment k X F p) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F) (hP : P ∈ X.image p)
    (hsmall : 2 * (block X p P).card ≤ X.card) :
    ∃ x ∈ X, (link F x).card < (X.card - 3).choose (k - 3) := by
  have hPS := hp.core_subset_block (by omega) hX hP
  by_cases he : block X p P = P
  · exact pair_only_block_low_degree hk hn hp hU hX hF hP he
  · have hnsub : ¬block X p P ⊆ P := fun hh => he (Subset.antisymm hh hPS)
    obtain ⟨x, hxS, hxP⟩ := not_subset.mp hnsub
    refine ⟨x, (mem_block.mp hxS).1, ?_⟩
    apply lt_of_le_of_lt (satellite_degree_bound hk hp hU hX hF hP hxS hxP)
    have hh := small_block_choose_gap hg hsmall
    simpa only [one_mul, show k - 4 + 1 = k - 3 by omega] using hh

theorem structured_low_degree_or_bound {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    {p : α → Finset α}
    (hk : 4 ≤ k) (hn : 2 * k ≤ X.card)
    (hg : growthThreshold 1 (k - 4) ≤ X.card)
    (hp : PairAssignment k X F p) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F) :
    F.card ≤ (X.card - 2).choose (k - 2) ∨
      ∃ x ∈ X, (link F x).card < (X.card - 3).choose (k - 3) := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < X.card)
  let P := p x
  have hP : P ∈ X.image p := mem_image_of_mem p hx
  have hSX : block X p P ⊆ X := fun _ h => (mem_block.mp h).1
  by_cases he : block X p P = X
  · left
    have hall : F ⊆ containing F P := by
      intro A hA
      have hAc := hU A hA
      obtain ⟨y, hyA⟩ := card_pos.mp (by omega : 0 < A.card)
      have hyS : y ∈ block X p P := by rw [he]; exact hX A hA hyA
      obtain ⟨hyX, hpy⟩ := mem_block.mp hyS
      exact mem_containing.mpr ⟨hA, hpy ▸ (hp y hyX).2.2 A hA hyA⟩
    have hh := containing_card_le hU hX ((hp.core hP).2.subset_support hX)
    rw [(hp.core hP).1] at hh
    exact (card_le_card hall).trans hh
  · right
    have hnsub : ¬X ⊆ block X p P := fun hh => he (Subset.antisymm hSX hh)
    obtain ⟨y, hyX, hyS⟩ := not_subset.mp hnsub
    let Q := p y
    have hQ : Q ∈ X.image p := mem_image_of_mem p hyX
    have hne : P ≠ Q := fun he => hyS (mem_block.mpr ⟨hyX, he.symm⟩)
    have hd : Disjoint (block X p P) (block X p Q) := by
      apply disjoint_left.mpr
      intro z hzP hzQ
      exact hne ((mem_block.mp hzP).2.symm.trans (mem_block.mp hzQ).2)
    have hsum : (block X p P).card + (block X p Q).card ≤ X.card := by
      rw [← card_union_of_disjoint hd]
      exact card_le_card (union_subset hSX (fun _ h => (mem_block.mp h).1))
    by_cases hsmall : 2 * (block X p P).card ≤ X.card
    · exact small_block_low_degree hk hn hg hp hU hX hF hP hsmall
    · exact small_block_low_degree hk hn hg hp hU hX hF hQ (by omega)

end Problem572
