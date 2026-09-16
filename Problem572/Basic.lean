import Mathlib

/-!
# Finite uniform families and links

Basic definitions for Frankl, "On families of finite sets no two of which
intersect in a singleton" (1977), pp. 125-126.
-/

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def Uniform (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = k

def Supported (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A ⊆ X

def NoSingletonIntersections (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1

def Intersecting (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

def link (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (F.filter (x ∈ ·)).image (fun A => A.erase x)

def restrict (F : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  F.filter (· ⊆ X)

def containing (F : Finset (Finset α)) (B : Finset α) : Finset (Finset α) :=
  F.filter (B ⊆ ·)

@[simp] theorem mem_link {F : Finset (Finset α)} {x : α} {A : Finset α} :
    A ∈ link F x ↔ x ∉ A ∧ insert x A ∈ F := by
  constructor
  · intro h
    obtain ⟨B, hB, rfl⟩ := mem_image.mp h
    obtain ⟨hB, hx⟩ := mem_filter.mp hB
    exact ⟨notMem_erase _ _, by simpa [insert_erase hx] using hB⟩
  · rintro ⟨hx, hA⟩
    apply mem_image.mpr
    exact ⟨insert x A, mem_filter.mpr ⟨hA, mem_insert_self _ _⟩,
      erase_insert hx⟩

@[simp] theorem mem_restrict {F : Finset (Finset α)} {X A : Finset α} :
    A ∈ restrict F X ↔ A ∈ F ∧ A ⊆ X := mem_filter

@[simp] theorem mem_containing {F : Finset (Finset α)} {A B : Finset α} :
    A ∈ containing F B ↔ A ∈ F ∧ B ⊆ A := mem_filter

omit [DecidableEq α] in
theorem Uniform.mono {k : ℕ} {F G : Finset (Finset α)}
    (h : Uniform k F) (hGF : G ⊆ F) : Uniform k G :=
  fun A hA => h A (hGF hA)

omit [DecidableEq α] in
theorem Supported.mono {X : Finset α} {F G : Finset (Finset α)}
    (h : Supported X F) (hGF : G ⊆ F) : Supported X G :=
  fun A hA => h A (hGF hA)

theorem NoSingletonIntersections.mono {F G : Finset (Finset α)}
    (h : NoSingletonIntersections F) (hGF : G ⊆ F) : NoSingletonIntersections G :=
  fun A hA B hB => h A (hGF hA) B (hGF hB)

theorem Uniform.link {k : ℕ} {F : Finset (Finset α)}
    (h : Uniform k F) (x : α) : Uniform (k - 1) (link F x) := by
  intro A hA
  obtain ⟨hx, hA⟩ := mem_link.mp hA
  have he := h _ hA
  rw [card_insert_of_notMem hx] at he
  omega

theorem Supported.link {X : Finset α} {F : Finset (Finset α)}
    (h : Supported X F) (x : α) : Supported (X.erase x) (link F x) := by
  intro A hA a ha
  obtain ⟨hx, hA⟩ := mem_link.mp hA
  exact mem_erase.mpr ⟨by rintro rfl; exact hx ha, h _ hA (mem_insert_of_mem ha)⟩

theorem link_intersecting {F : Finset (Finset α)}
    (hF : NoSingletonIntersections F) (x : α) : Intersecting (link F x) := by
  intro A hA B hB
  obtain ⟨hxA, hA⟩ := mem_link.mp hA
  obtain ⟨hxB, hB⟩ := mem_link.mp hB
  by_contra h
  have he : A ∩ B = ∅ := not_nonempty_iff_eq_empty.mp h
  have hc := hF _ hA _ hB
  have hi : insert x A ∩ insert x B = {x} := by
    ext a
    have : ¬(a ∈ A ∧ a ∈ B) := by
      intro ha
      have := mem_inter.mpr ha
      rw [he] at this
      exact notMem_empty _ this
    simp only [mem_inter, mem_insert, mem_singleton]
    tauto
  exact hc (by rw [hi, card_singleton])

omit [DecidableEq α] in
theorem uniform_card_le {k : ℕ} {X : Finset α} {F : Finset (Finset α)}
    (hU : Uniform k F) (hX : Supported X F) : F.card ≤ X.card.choose k := by
  rw [← card_powersetCard]
  exact card_le_card (fun A hA => mem_powersetCard.mpr ⟨hX A hA, hU A hA⟩)

theorem card_link (F : Finset (Finset α)) (x : α) :
    (link F x).card = (F.filter (x ∈ ·)).card := by
  apply card_image_iff.mpr
  intro A hA B hB he
  have hxA := (mem_filter.mp hA).2
  have hxB := (mem_filter.mp hB).2
  simpa [insert_erase hxA, insert_erase hxB] using congrArg (insert x) he

end Problem572
