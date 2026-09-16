import Problem572.Basic

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

theorem intersecting_card_le {k : ℕ} {F : Finset (Finset α)} {X : Finset α}
    (hU : Uniform k F) (hX : Supported X F) (hI : Intersecting F)
    (hn : 2 * k ≤ X.card) : F.card ≤ (X.card - 1).choose (k - 1) := by
  classical
  let e := Fintype.equivFin X
  let f : Finset α → Finset (Fin (Fintype.card X)) :=
    fun A => (A.subtype (· ∈ X)).map e.toEmbedding
  have hcard : ∀ A ∈ F, (f A).card = A.card := by
    intro A hA
    simp only [f, card_map, card_subtype]
    rw [filter_eq_self.mpr (hX A hA)]
  have hinj : Set.InjOn f (F : Set (Finset α)) := by
    intro A hA B hB he
    have hh := Finset.map_injective e.toEmbedding he
    have hh' := congrArg (Finset.map (Function.Embedding.subtype (· ∈ X))) hh
    simpa [subtype_map_of_mem (hX A hA), subtype_map_of_mem (hX B hB)] using hh'
  have hinter : (F.image f : Set (Finset (Fin (Fintype.card X)))).Intersecting := by
    intro A hA B hB hd
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hA
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
    obtain ⟨x, hx⟩ := hI C hC D hD
    obtain ⟨hxC, hxD⟩ := mem_inter.mp hx
    let y : X := ⟨x, hX C hC hxC⟩
    have hyC : e y ∈ f C := mem_map.mpr ⟨y, mem_subtype.mpr hxC, rfl⟩
    have hyD : e y ∈ f D := mem_map.mpr ⟨y, mem_subtype.mpr hxD, rfl⟩
    exact disjoint_left.mp hd hyC hyD
  have hsize : (F.image f : Set (Finset (Fin (Fintype.card X)))).Sized k := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact (hcard B hB).trans (hU B hB)
  have hh := Finset.erdos_ko_rado hinter hsize (by
    simpa only [Fintype.card_coe] using (show k ≤ X.card / 2 by omega))
  simpa only [card_image_iff.mpr hinj, Fintype.card_coe] using hh

theorem sum_link_card {k : ℕ} {F : Finset (Finset α)} {X : Finset α}
    (hU : Uniform k F) (hX : Supported X F) :
    ∑ x ∈ X, (link F x).card = F.card * k := by
  simp_rw [card_link]
  change (∑ x ∈ X, (F.bipartiteAbove (fun x A => x ∈ A) x).card) = _
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have hh : ∀ A ∈ F, (X.bipartiteBelow (fun x A => x ∈ A) A).card = k := by
    intro A hA
    have he : X.filter (· ∈ A) = A := by
      ext x
      exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hX A hA h, h⟩⟩
    simpa only [bipartiteBelow, he] using hU A hA
  simp_rw [sum_congr rfl hh]
  simp

theorem singleton_free_card_bound {k : ℕ} {F : Finset (Finset α)} {X : Finset α}
    (hU : Uniform k F) (hX : Supported X F) (hF : NoSingletonIntersections F)
    (hn : 2 * k ≤ X.card) :
    F.card * k ≤ X.card * (X.card - 2).choose (k - 2) := by
  rw [← sum_link_card hU hX]
  calc
    (∑ x ∈ X, (link F x).card) ≤ ∑ _x ∈ X, (X.card - 2).choose (k - 2) := by
      apply sum_le_sum
      intro x hx
      have hc : (X.erase x).card = X.card - 1 := card_erase_of_mem hx
      have hh := intersecting_card_le (hU.link x) (hX.link x) (link_intersecting hF x)
        (by rw [hc]; omega)
      simpa only [hc, Nat.sub_sub] using hh
    _ = _ := by simp

end Problem572
