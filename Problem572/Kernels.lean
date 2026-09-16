import Problem572.Sunflower
import Problem572.Counting

/-!
# Kernels with bounded avoidance

The local argument only uses a kernel through its ability to avoid a bounded
set of forbidden points. This formulation makes the finite blocking arguments
explicit, without requiring an asymptotic matching theorem as an axiom.
-/

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def Rich (r : ℕ) (F : Finset (Finset α)) (B : Finset α) : Prop :=
  ∀ S : Finset α, S.card ≤ r → Disjoint S B →
    ∃ A ∈ F, B ⊆ A ∧ Disjoint S A

omit [DecidableEq α] in
theorem Rich.of_mem {r : ℕ} {F : Finset (Finset α)} {B : Finset α}
    (hB : B ∈ F) : Rich r F B :=
  fun _ _ hd => ⟨B, hB, Subset.rfl, hd⟩

omit [DecidableEq α] in
theorem Rich.exists_superset {r : ℕ} {F : Finset (Finset α)} {B : Finset α}
    (h : Rich r F B) : ∃ A ∈ F, B ⊆ A := by
  obtain ⟨A, hA, hBA, _⟩ := h ∅ (by simp) (by simp)
  exact ⟨A, hA, hBA⟩

omit [DecidableEq α] in
theorem Rich.subset_support {r : ℕ} {F : Finset (Finset α)} {B X : Finset α}
    (h : Rich r F B) (hX : Supported X F) : B ⊆ X := by
  obtain ⟨A, hA, hBA⟩ := h.exists_superset
  exact hBA.trans (hX A hA)

omit [DecidableEq α] in
theorem Rich.card_le {r k : ℕ} {F : Finset (Finset α)} {B : Finset α}
    (h : Rich r F B) (hU : Uniform k F) : B.card ≤ k := by
  obtain ⟨A, hA, hBA⟩ := h.exists_superset
  simpa [hU A hA] using card_le_card hBA

theorem KernelWitness.rich {r t : ℕ} {F : Finset (Finset α)} {B : Finset α}
    (h : KernelWitness F B t) (hrt : r < t) : Rich r F B := by
  intro S hS hd
  obtain ⟨A, hA, hBA, hAS⟩ := h.avoid
    ((card_le_card sdiff_subset).trans_lt (hS.trans_lt hrt))
  refine ⟨A, hA, hBA, disjoint_left.mpr ?_⟩
  intro a haS haA
  have haB : a ∉ B := fun ha => disjoint_left.mp hd haS ha
  exact disjoint_left.mp hAS (mem_sdiff.mpr ⟨haA, haB⟩) haS

theorem not_rich_iff {r : ℕ} {F : Finset (Finset α)} {B : Finset α} :
    ¬Rich r F B ↔ ∃ S : Finset α, S.card ≤ r ∧ Disjoint S B ∧
      ∀ A ∈ F, B ⊆ A → (S ∩ A).Nonempty := by
  classical
  simp only [Rich, not_forall, not_exists, not_and, not_nonempty_iff_eq_empty]
  simp only [← disjoint_iff_inter_eq_empty, not_disjoint_iff_nonempty_inter]
  simp only [exists_prop]

theorem Rich.inter_eq {r : ℕ} {F : Finset (Finset α)} {B H : Finset α}
    (h : Rich r F B) (hH : (H \ B).card ≤ r) :
    ∃ A ∈ F, B ⊆ A ∧ A ∩ H = B ∩ H := by
  obtain ⟨A, hA, hBA, hd⟩ := h (H \ B) hH sdiff_disjoint
  refine ⟨A, hA, hBA, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨haA, haH⟩ := mem_inter.mp ha
    have haB : a ∈ B := by
      by_contra hn
      exact disjoint_left.mp hd (mem_sdiff.mpr ⟨haH, hn⟩) haA
    exact mem_inter.mpr ⟨haB, haH⟩
  · intro ha
    exact mem_inter.mpr ⟨hBA (mem_inter.mp ha).1, (mem_inter.mp ha).2⟩

theorem Rich.inter_member_ne_one {k : ℕ} {F : Finset (Finset α)} {B A : Finset α}
    (h : Rich k F B) (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (hA : A ∈ F) : (B ∩ A).card ≠ 1 := by
  obtain ⟨C, hC, _, he⟩ := h.inter_eq
    ((card_le_card sdiff_subset).trans_eq (hU A hA))
  rw [← he]
  exact hF C hC A hA

theorem Rich.inter_ne_one {k : ℕ} {F : Finset (Finset α)} {B C : Finset α}
    (hB : Rich k F B) (hC : Rich k F C)
    (hU : Uniform k F) (hF : NoSingletonIntersections F) :
    (B ∩ C).card ≠ 1 := by
  obtain ⟨A, hA, _, he⟩ := hB.inter_eq
    ((card_le_card sdiff_subset).trans (hC.card_le hU))
  have hh := hC.inter_member_ne_one hU hF hA
  rw [inter_comm C A, he] at hh
  exact hh

omit [DecidableEq α] in
theorem Rich.mono_parameter {r s : ℕ} {F : Finset (Finset α)} {B : Finset α}
    (h : Rich r F B) (hsr : s ≤ r) : Rich s F B :=
  fun S hS hd => h S (hS.trans hsr) hd

theorem not_rich_singleton {k : ℕ} {F : Finset (Finset α)}
    (hU : Uniform k F) (hF : NoSingletonIntersections F) (x : α) :
    ¬Rich k F {x} := by
  intro h
  obtain ⟨A, hA, hx⟩ := h.exists_superset
  have := h.inter_member_ne_one hU hF hA
  rw [inter_eq_left.mpr hx, card_singleton] at this
  exact this rfl

theorem Rich.meets_blocker {r : ℕ} {F : Finset (Finset α)} {B C S : Finset α}
    (h : Rich r F B) (hCB : C ⊆ B) (hS : S.card ≤ r)
    (hblock : ∀ A ∈ F, C ⊆ A → (S ∩ A).Nonempty) :
    (S ∩ B).Nonempty := by
  by_contra hn
  have hd : Disjoint S B := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  obtain ⟨A, hA, hBA, hSA⟩ := h S hS hd
  exact (not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp hSA))
    (hblock A hA (hCB.trans hBA))

theorem blocker_in_support {r : ℕ} {F : Finset (Finset α)} {B X : Finset α}
    (h : ¬Rich r F B) (hX : Supported X F) :
    ∃ S : Finset α, S ⊆ X ∧ S.card ≤ r ∧ Disjoint S B ∧
      ∀ A ∈ F, B ⊆ A → (S ∩ A).Nonempty := by
  obtain ⟨S, hS, hd, hb⟩ := not_rich_iff.mp h
  refine ⟨S ∩ X, inter_subset_right, (card_le_card inter_subset_left).trans hS,
    hd.mono_left inter_subset_left, ?_⟩
  intro A hA hBA
  obtain ⟨a, ha⟩ := hb A hA hBA
  obtain ⟨haS, haA⟩ := mem_inter.mp ha
  exact ⟨a, mem_inter.mpr ⟨mem_inter.mpr ⟨haS, hX A hA haA⟩, haA⟩⟩

theorem extension_cover {r : ℕ} {F : Finset (Finset α)} {B X : Finset α}
    (h : ¬Rich r F B) (hX : Supported X F) (hBX : B ⊆ X) :
    ∃ C : Finset (Finset α), C.card ≤ r ∧
      (∀ D ∈ C, B ⊆ D ∧ D ⊆ X ∧ D.card = B.card + 1) ∧
      (∀ A ∈ F, B ⊆ A → ∃ D ∈ C, D ⊆ A) ∧
      (∀ A, Rich r F A → B ⊆ A → ∃ D ∈ C, D ⊆ A) := by
  obtain ⟨S, hSX, hS, hd, hb⟩ := blocker_in_support h hX
  refine ⟨S.image (fun a => insert a B), (card_image_le).trans hS, ?_, ?_, ?_⟩
  · intro D hD
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hD
    have haB : a ∉ B := fun haB => disjoint_left.mp hd ha haB
    exact ⟨subset_insert _ _, insert_subset (hSX ha) hBX, card_insert_of_notMem haB⟩
  · intro A hA hBA
    obtain ⟨a, ha⟩ := hb A hA hBA
    obtain ⟨haS, haA⟩ := mem_inter.mp ha
    exact ⟨insert a B, mem_image_of_mem _ haS, insert_subset haA hBA⟩
  · intro A hA hBA
    obtain ⟨a, ha⟩ := hA.meets_blocker hBA hS hb
    obtain ⟨haS, haA⟩ := mem_inter.mp ha
    exact ⟨insert a B, mem_image_of_mem _ haS, insert_subset haA hBA⟩

theorem nonrich_count {r k : ℕ} {F : Finset (Finset α)} {B X : Finset α}
    (h : ¬Rich r F B) (hU : Uniform k F) (hX : Supported X F) (hBX : B ⊆ X) :
    (containing F B).card ≤
      r * (X.card - (B.card + 1)).choose (k - (B.card + 1)) := by
  obtain ⟨C, hC, hCs, hc, _⟩ := extension_cover h hX hBX
  calc
    (containing F B).card ≤ ∑ D ∈ C, (containing F D).card :=
      card_le_sum_of_cover _ _ _ (by
        intro A hA
        obtain ⟨hA, hBA⟩ := mem_containing.mp hA
        obtain ⟨D, hD, hDA⟩ := hc A hA hBA
        exact ⟨D, hD, mem_containing.mpr ⟨hA, hDA⟩⟩)
    _ ≤ ∑ _D ∈ C, (X.card - (B.card + 1)).choose (k - (B.card + 1)) := by
      apply sum_le_sum
      intro D hD
      obtain ⟨_, hDX, hDc⟩ := hCs D hD
      simpa [hDc] using containing_card_le hU hX hDX
    _ = C.card * (X.card - (B.card + 1)).choose (k - (B.card + 1)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hC

theorem rich_of_large_count {r k : ℕ} {F : Finset (Finset α)} {B X : Finset α}
    (hU : Uniform k F) (hX : Supported X F) (hBX : B ⊆ X)
    (h : r * (X.card - (B.card + 1)).choose (k - (B.card + 1)) <
      (containing F B).card) : Rich r F B := by
  by_contra hn
  exact (not_lt_of_ge (nonrich_count hn hU hX hBX)) h

theorem uniform_extension_cover (r d : ℕ) {F : Finset (Finset α)}
    {B X : Finset α} (hX : Supported X F) (hBX : B ⊆ X)
    (hn : ∀ D, B ⊆ D → D.card < B.card + d → ¬Rich r F D) :
    ∃ C : Finset (Finset α), C.card ≤ r ^ d ∧
      (∀ D ∈ C, B ⊆ D ∧ D ⊆ X ∧ D.card = B.card + d) ∧
      (∀ A ∈ F, B ⊆ A → ∃ D ∈ C, D ⊆ A) ∧
      (∀ A, Rich r F A → B ⊆ A → ∃ D ∈ C, D ⊆ A) := by
  classical
  induction d generalizing B with
  | zero =>
    refine ⟨{B}, by simp, ?_, ?_, ?_⟩
    · intro D hD
      obtain rfl := mem_singleton.mp hD
      exact ⟨Subset.rfl, hBX, by simp⟩
    · intro A _ hBA
      exact ⟨B, mem_singleton_self _, hBA⟩
    · intro A _ hBA
      exact ⟨B, mem_singleton_self _, hBA⟩
  | succ d ih =>
    obtain ⟨C, hC, hCs, hcF, hcR⟩ :=
      extension_cover (hn B Subset.rfl (by omega)) hX hBX
    have hex : ∀ D ∈ C, ∃ E : Finset (Finset α), E.card ≤ r ^ d ∧
        (∀ Q ∈ E, D ⊆ Q ∧ Q ⊆ X ∧ Q.card = D.card + d) ∧
        (∀ A ∈ F, D ⊆ A → ∃ Q ∈ E, Q ⊆ A) ∧
        (∀ A, Rich r F A → D ⊆ A → ∃ Q ∈ E, Q ⊆ A) := by
      intro D hD
      obtain ⟨hBD, hDX, hDc⟩ := hCs D hD
      apply ih hDX
      intro Q hDQ hQc
      apply hn Q (hBD.trans hDQ)
      omega
    choose E hE using hex
    let Es : Finset (Finset α) := C.attach.biUnion (fun D => E D.val D.property)
    have hEs : ∀ Q ∈ Es, ∃ D, ∃ hD : D ∈ C, Q ∈ E D hD := by
      intro Q hQ
      obtain ⟨D, _, hQD⟩ := mem_biUnion.mp hQ
      exact ⟨D.val, D.property, hQD⟩
    refine ⟨Es, ?_, ?_, ?_, ?_⟩
    · calc
        Es.card ≤ ∑ D ∈ C.attach, (E D.val D.property).card := card_biUnion_le
        _ ≤ ∑ _D ∈ C.attach, r ^ d := sum_le_sum (fun D _ => (hE D.val D.property).1)
        _ = C.card * r ^ d := by simp
        _ ≤ r * r ^ d := Nat.mul_le_mul_right _ hC
        _ = r ^ (d + 1) := by ring
    · intro Q hQ
      obtain ⟨D, hD, hQD⟩ := hEs Q hQ
      obtain ⟨hBD, _, hDc⟩ := hCs D hD
      obtain ⟨hDQ, hQX, hQc⟩ := (hE D hD).2.1 Q hQD
      exact ⟨hBD.trans hDQ, hQX, by omega⟩
    · intro A hA hBA
      obtain ⟨D, hD, hDA⟩ := hcF A hA hBA
      obtain ⟨Q, hQ, hQA⟩ := (hE D hD).2.2.1 A hA hDA
      exact ⟨Q, mem_biUnion.mpr ⟨⟨D, hD⟩, mem_attach _ _, hQ⟩, hQA⟩
    · intro A hA hBA
      obtain ⟨D, hD, hDA⟩ := hcR A hA hBA
      obtain ⟨Q, hQ, hQA⟩ := (hE D hD).2.2.2 A hA hDA
      exact ⟨Q, mem_biUnion.mpr ⟨⟨D, hD⟩, mem_attach _ _, hQ⟩, hQA⟩

end Problem572
