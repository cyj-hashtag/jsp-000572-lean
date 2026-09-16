import Problem572.LocalStructure
import Problem572.RichExtension

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

theorem no_small_rich_at {k : ℕ} {F : Finset (Finset α)} {x : α}
    (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (hp : ∀ P, x ∈ P → P.card = 2 → ¬Rich k F P) :
    ∀ D, x ∈ D → D.card < 3 → ¬Rich k F D := by
  intro D hxD hc hD
  have hpos : 0 < D.card := card_pos.mpr ⟨x, hxD⟩
  by_cases h2 : D.card = 2
  · exact hp D hxD h2 hD
  · have he : ({x} : Finset α) = D :=
      eq_of_subset_of_card_le (singleton_subset_iff.mpr hxD) (by simp; omega)
    exact not_rich_singleton hU hF x (he.symm ▸ hD)

theorem triple_cover_at {k : ℕ} {F : Finset (Finset α)} {X : Finset α} {x : α}
    (hx : x ∈ X) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F)
    (hp : ∀ P, x ∈ P → P.card = 2 → ¬Rich k F P) :
    ∃ C : Finset (Finset α), C.card ≤ k ^ 2 ∧
      (∀ T ∈ C, x ∈ T ∧ T ⊆ X ∧ T.card = 3) ∧
      (∀ A ∈ F, x ∈ A → ∃ T ∈ C, T ⊆ A) ∧
      (∀ T, x ∈ T → T.card = 3 → Rich k F T → T ∈ C) := by
  obtain ⟨C, hC, hCs, hcover, hrich⟩ := uniform_extension_cover k 2 hX
    (singleton_subset_iff.mpr hx) (by
      intro D hxD hDc
      exact no_small_rich_at hU hF hp D (hxD (mem_singleton_self x))
        (by simpa using hDc))
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨hxT, hTX, hTc⟩ := hCs T hT
    exact ⟨hxT (mem_singleton_self x), hTX, by simpa using hTc⟩
  · intro A hA hxA
    exact hcover A hA (singleton_subset_iff.mpr hxA)
  · intro T hxT hTc hTr
    obtain ⟨D, hD, hDT⟩ := hrich T hTr (singleton_subset_iff.mpr hxT)
    have hDc : D.card = 3 := by simpa using (hCs D hD).2.2
    have he : D = T := eq_of_subset_of_card_le hDT (by omega)
    exact he ▸ hD

theorem Rich.forced_subset {k : ℕ} {F : Finset (Finset α)} {B C : Finset α} {x : α}
    (hB : Rich k F B) (hx : x ∈ B) (hC : C.card ≤ k)
    (hforce : ∀ A ∈ F, x ∈ A → C ⊆ A) : C ⊆ B := by
  obtain ⟨A, hA, hBA, he⟩ := hB.inter_eq ((card_le_card sdiff_subset).trans hC)
  have hCA := hforce A hA (hBA hx)
  intro y hy
  have : y ∈ A ∩ C := mem_inter.mpr ⟨hCA hy, hy⟩
  rw [he] at this
  exact (mem_inter.mp this).1

-- A rich extension outside all triples through x rules out a member that
-- contains x but only two points of the selected triple.
theorem forcing_triple_of_large_count {k : ℕ} {F : Finset (Finset α)}
    {X T H : Finset α} {x : α}
    (hk : 4 ≤ k) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F) (hxT : x ∈ T) (hTc : T.card = 3)
    (hT : Rich k F T)
    (hH : ∀ B, x ∈ B → B.card = 3 → Rich k F B → B ⊆ H)
    (hcores : ∀ z ∈ X, ∃ B, z ∈ B ∧ B.card ≤ 3 ∧ Rich k F B)
    (hlarge : (H.card + 2 * k) * X.card ^ (k - 4) < (containing F T).card) :
    ∀ A ∈ F, x ∈ A → T ⊆ A := by
  intro A hA hxA
  by_contra hTA
  have hi : (T ∩ A).card = 2 := by
    have hp : 0 < (T ∩ A).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxT, hxA⟩⟩
    have hn := hT.inter_member_ne_one hU hF hA
    have hlt : (T ∩ A).card < T.card :=
      card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, fun he =>
        hTA (inter_eq_left.mp he)⟩)
    omega
  have hbound : ((H ∪ A).card + k) * X.card ^ (k - 4) <
      (containing F T).card := by
    apply lt_of_le_of_lt _ hlarge
    apply Nat.mul_le_mul_right
    have hh := card_union_le H A
    rw [hU A hA] at hh
    omega
  obtain ⟨z, hzX, hzT, hzHA, hQ⟩ := rich_extension_outside hk hU hX
    (hT.subset_support hX) hTc hbound
  have hzH : z ∉ H := fun hz => hzHA (mem_union_left _ hz)
  have hzA : z ∉ A := fun hz => hzHA (mem_union_right _ hz)
  obtain ⟨B, hzB, hBc, hB⟩ := hcores z hzX
  have heQ : insert z T ∩ B = insert z (T ∩ B) := by
    ext y
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨hy | hy, hyB⟩
      · exact Or.inl hy
      · exact Or.inr ⟨hy, hyB⟩
    · rintro (rfl | ⟨hyT, hyB⟩)
      · exact ⟨Or.inl rfl, hzB⟩
      · exact ⟨Or.inr hyT, hyB⟩
  have hzI : z ∉ T ∩ B := fun hz => hzT (mem_inter.mp hz).1
  have hI0 : (T ∩ B).card ≠ 0 := by
    intro h0
    have hn := hQ.inter_ne_one hB hU hF
    rw [heQ, card_insert_of_notMem hzI, h0] at hn
    exact hn rfl
  have hI1 := hT.inter_ne_one hB hU hF
  have hIB : insert z (T ∩ B) ⊆ B := insert_subset hzB inter_subset_right
  have hIc := card_le_card hIB
  rw [card_insert_of_notMem hzI] at hIc
  have hI2 : (T ∩ B).card = 2 := by omega
  have hB3 : B.card = 3 := by omega
  have hxB : x ∉ B := by
    intro hxB
    exact hzH (hH B hxB hB3 hB hzB)
  have hBI : T ∩ B = T.erase x := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨hyT, hyB⟩ := mem_inter.mp hy
      exact mem_erase.mpr ⟨by rintro rfl; exact hxB hyB, hyT⟩
    · rw [card_erase_of_mem hxT, hTc, hI2]
  have hBeq : B = insert z (T.erase x) := by
    symm
    rw [← hBI]
    apply eq_of_subset_of_card_le hIB
    rw [card_insert_of_notMem hzI, hI2, hB3]
  have heA : B ∩ A = (T ∩ A).erase x := by
    rw [hBeq]
    ext y
    simp only [mem_inter, mem_insert, mem_erase]
    constructor
    · rintro ⟨rfl | hy, hyA⟩
      · exact (hzA hyA).elim
      · exact ⟨hy.1, hy.2, hyA⟩
    · rintro ⟨hyx, hyT, hyA⟩
      exact ⟨Or.inr ⟨hyx, hyT⟩, hyA⟩
  have hn := hB.inter_member_ne_one hU hF hA
  rw [heA, card_erase_of_mem (mem_inter.mpr ⟨hxT, hxA⟩), hi] at hn
  exact hn rfl

def rigidityConstant (k : ℕ) : ℕ := k ^ 2 * (3 * k ^ 2 + 2 * k)

theorem high_degree_forces_triple {k : ℕ} {F : Finset (Finset α)}
    {X : Finset α} {x : α}
    (hk : 4 ≤ k) (hx : x ∈ X) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F)
    (hp : ∀ P, x ∈ P → P.card = 2 → ¬Rich k F P)
    (hcores : ∀ z ∈ X, ∃ B, z ∈ B ∧ B.card ≤ 3 ∧ Rich k F B)
    (hdeg : rigidityConstant k * X.card ^ (k - 4) < (link F x).card) :
    ∃ T, x ∈ T ∧ T.card = 3 ∧ Rich k F T ∧
      ∀ A ∈ F, x ∈ A → T ⊆ A := by
  classical
  obtain ⟨C, hC, hCs, hcover, hrich⟩ := triple_cover_at hx hU hX hF hp
  let L := 3 * k ^ 2 + 2 * k
  have hex : ∃ T ∈ C, L * X.card ^ (k - 4) < (containing F T).card := by
    by_contra! hn
    have hc : (containing F {x}).card ≤ k ^ 2 * (L * X.card ^ (k - 4)) := by
      calc
        (containing F {x}).card ≤ ∑ T ∈ C, (containing F T).card :=
          card_le_sum_of_cover _ _ _ (by
            intro A hA
            obtain ⟨hA, hxA⟩ := mem_containing.mp hA
            obtain ⟨T, hT, hTA⟩ := hcover A hA (hxA (mem_singleton_self x))
            exact ⟨T, hT, mem_containing.mpr ⟨hA, hTA⟩⟩)
        _ ≤ ∑ _T ∈ C, L * X.card ^ (k - 4) := sum_le_sum hn
        _ = C.card * (L * X.card ^ (k - 4)) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hC
    have hl : (link F x).card = (containing F {x}).card := by
      rw [card_link]
      simp [containing, singleton_subset_iff]
    rw [hl] at hdeg
    exact (not_lt_of_ge hc) (by simpa [rigidityConstant, L, Nat.mul_assoc] using hdeg)
  obtain ⟨T, hTC, hlarge⟩ := hex
  obtain ⟨hxT, hTX, hTc⟩ := hCs T hTC
  have hT : Rich k F T := by
    apply rich_of_large_count hU hX hTX
    rw [hTc]
    apply lt_of_le_of_lt _ hlarge
    apply Nat.mul_le_mul
    · dsimp [L]
      omega
    · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  let H := C.biUnion id
  have hHc : H.card ≤ 3 * k ^ 2 := by
    calc
      H.card ≤ ∑ T ∈ C, T.card := card_biUnion_le
      _ = C.card * 3 := by simp_rw [sum_congr rfl (fun T hT => (hCs T hT).2.2)]; simp
      _ ≤ 3 * k ^ 2 := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right 3 hC
  refine ⟨T, hxT, hTc, hT, forcing_triple_of_large_count (H := H) hk hU hX hF hxT hTc hT ?_ hcores ?_⟩
  · intro B hxB hBc hBr b hb
    exact mem_biUnion.mpr ⟨B, hrich B hxB hBc hBr, hb⟩
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.add_le_add_right hHc _)) hlarge

theorem high_degrees_have_small_cores {k : ℕ} {F : Finset (Finset α)} {X : Finset α}
    (hU : Uniform k F) (hX : Supported X F) (hF : NoSingletonIntersections F)
    (hdeg : ∀ x ∈ X, rigidityConstant k * X.card ^ (k - 4) < (link F x).card) :
    ∀ x ∈ X, ∃ B, x ∈ B ∧ B.card ≤ 3 ∧ Rich k F B := by
  intro x hx
  by_cases hp : ∃ P, x ∈ P ∧ P.card = 2 ∧ Rich k F P
  · obtain ⟨P, hxP, hPc, hP⟩ := hp
    exact ⟨P, hxP, by omega, hP⟩
  · push_neg at hp
    have hnum : k ^ 3 * (X.card - 4).choose (k - 4) ≤
        rigidityConstant k * X.card ^ (k - 4) := by
      apply Nat.mul_le_mul
      · calc
          k ^ 3 = k ^ 2 * k := by ring
          _ ≤ rigidityConstant k := Nat.mul_le_mul_left _ (by omega)
      · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
    obtain ⟨T, hxT, hTc, hT⟩ := high_degree_has_rich_triple hx hX hU
      (no_small_rich_at hU hF hp) (hnum.trans_lt (hdeg x hx))
    exact ⟨T, hxT, by omega, hT⟩

theorem pair_subset_rich_of_mem {k : ℕ} {F : Finset (Finset α)} {P T : Finset α} {x : α}
    (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (hPc : P.card = 2) (hP : Rich k F P) (hT : Rich k F T)
    (hxP : x ∈ P) (hxT : x ∈ T) : P ⊆ T := by
  have hn := hP.inter_ne_one hT hU hF
  have hpos : 0 < (P ∩ T).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxP, hxT⟩⟩
  have hle : (P ∩ T).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hPc
  have he : P ∩ T = P := eq_of_subset_of_card_le inter_subset_left (by omega)
  exact inter_eq_left.mp he

theorem high_degree_structure {k : ℕ} {F : Finset (Finset α)} {X : Finset α}
    (hk : 4 ≤ k) (hU : Uniform k F) (hX : Supported X F)
    (hF : NoSingletonIntersections F)
    (hdeg : ∀ x ∈ X, rigidityConstant k * X.card ^ (k - 4) < (link F x).card) :
    (∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧
      (F.filter (fun A => x ∈ A ∨ y ∈ A)).card ≤ (X.card - 3).choose (k - 3)) ∨
    (∀ x ∈ X, ∃ P, P.card = 2 ∧ Rich k F P ∧ ∀ A ∈ F, x ∈ A → P ⊆ A) := by
  classical
  by_cases hs : ∀ x ∈ X, ∃ P, P.card = 2 ∧ Rich k F P ∧
      ∀ A ∈ F, x ∈ A → P ⊆ A
  · exact Or.inr hs
  left
  push_neg at hs
  obtain ⟨x, hx, hbad⟩ := hs
  have hcores := high_degrees_have_small_cores hU hX hF hdeg
  have hp : ∀ P, x ∈ P → P.card = 2 → ¬Rich k F P := by
    intro P hxP hPc hP
    obtain ⟨A, hA, hxA, hPA⟩ := hbad P hPc hP
    rcases pair_kernel_all_or_none hP hPc hU hF hA with hd | hh
    · exact disjoint_left.mp hd hxP hxA
    · exact hPA hh
  obtain ⟨T, hxT, hTc, hT, hforce⟩ := high_degree_forces_triple hk hx hU hX hF hp hcores (hdeg x hx)
  have hnp : ∀ P, P ⊆ T → P.card = 2 → ¬Rich k F P := by
    intro P hPT hPc hP
    obtain ⟨Q, _, hQc, hQ, hforceQ⟩ := rich_triple_contains_pair hTc hT hU hF
      ⟨P, hPT, hPc, hP⟩
    obtain ⟨A, hA, hxA, hQA⟩ := hbad Q hQc hQ
    exact hQA (hforceQ A hA ⟨x, mem_inter.mpr ⟨hxT, hxA⟩⟩)
  have hnempty : (T.erase x).Nonempty := by
    rw [← card_pos, card_erase_of_mem hxT, hTc]
    decide
  obtain ⟨y, hy⟩ := hnempty
  obtain ⟨hyx, hyT⟩ := mem_erase.mp hy
  have hyX := hT.subset_support hX hyT
  have hpy : ∀ P, y ∈ P → P.card = 2 → ¬Rich k F P := by
    intro P hyP hPc hP
    exact hnp P (pair_subset_rich_of_mem hU hF hPc hP hT hyP hyT) hPc hP
  obtain ⟨Q, hyQ, hQc, hQ, hforceQ⟩ := high_degree_forces_triple hk hyX hU hX hF hpy hcores (hdeg y hyX)
  have hQT : Q ⊆ T := hT.forced_subset hyT (by omega) hforceQ
  have he : Q = T := eq_of_subset_of_card_le hQT (by omega)
  subst Q
  refine ⟨x, hx, y, hyX, Ne.symm hyx, ?_⟩
  calc
    (F.filter (fun A => x ∈ A ∨ y ∈ A)).card ≤ (containing F T).card :=
      card_le_card (by
        intro A hA
        obtain ⟨hA, hxA | hyA⟩ := mem_filter.mp hA
        · exact mem_containing.mpr ⟨hA, hforce A hA hxA⟩
        · exact mem_containing.mpr ⟨hA, hforceQ A hA hyA⟩)
    _ ≤ (X.card - 3).choose (k - 3) := by
      simpa [hTc] using containing_card_le hU hX (hT.subset_support hX)

end Problem572
