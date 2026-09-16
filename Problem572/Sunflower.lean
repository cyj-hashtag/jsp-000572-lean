import Problem572.Basic

/-!
# Sunflowers and kernel witnesses

Kernel witnesses may repeat a member equal to the kernel, as in Frankl's
definition of G*. A sunflower subfamily additionally has distinct members.
-/

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def KernelWitness (F : Finset (Finset α)) (B : Finset α) (t : ℕ) : Prop :=
  ∃ f : Fin t → Finset α,
    (∀ i, f i ∈ F) ∧ (∀ i, B ⊆ f i) ∧
    ∀ i j, i ≠ j → f i ∩ f j = B

def Sunflower (S : Finset (Finset α)) (B : Finset α) : Prop :=
  (∀ A ∈ S, B ⊆ A) ∧ ∀ A ∈ S, ∀ C ∈ S, A ≠ C → A ∩ C = B

theorem KernelWitness.of_mem {F : Finset (Finset α)} {B : Finset α}
    (h : B ∈ F) (t : ℕ) : KernelWitness F B t := by
  exact ⟨fun _ => B, fun _ => h, fun _ => Subset.rfl, fun _ _ _ => inter_self B⟩

theorem KernelWitness.mono {F G : Finset (Finset α)} {B : Finset α} {t : ℕ}
    (h : KernelWitness F B t) (hFG : F ⊆ G) : KernelWitness G B t := by
  obtain ⟨f, hf, hB, hi⟩ := h
  exact ⟨f, fun i => hFG (hf i), hB, hi⟩

theorem KernelWitness.reduce {F : Finset (Finset α)} {B : Finset α} {s t : ℕ}
    (h : KernelWitness F B t) (hst : s ≤ t) : KernelWitness F B s := by
  obtain ⟨f, hf, hB, hi⟩ := h
  refine ⟨fun i => f (Fin.castLE hst i), fun i => hf _, fun i => hB _, ?_⟩
  intro i j hij
  apply hi
  intro he
  exact hij (Fin.ext (congrArg (fun z : Fin t => z.val) he))

theorem exists_disjoint_of_pairwiseDisjoint {t : ℕ} (P : Fin t → Finset α)
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (H : Finset α) (hH : H.card < t) : ∃ i, Disjoint (P i) H := by
  classical
  by_contra! hn
  have hn' : ∀ i, ∃ a, a ∈ P i ∧ a ∈ H := by
    intro i
    exact not_disjoint_iff.mp (hn i)
  choose a ha hHmem using hn'
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hP i j hne) (ha i) (hij.symm ▸ ha j)
  have hle : t ≤ H.card := by
    calc
      t = (univ : Finset (Fin t)).card := by simp
      _ = ((univ : Finset (Fin t)).image a).card :=
        (card_image_of_injective _ hinj).symm
      _ ≤ H.card := card_le_card (by
        intro b hb
        obtain ⟨i, _, rfl⟩ := mem_image.mp hb
        exact hHmem i)
  omega

theorem KernelWitness.avoid {F : Finset (Finset α)} {B H : Finset α} {t : ℕ}
    (h : KernelWitness F B t) (hH : (H \ B).card < t) :
    ∃ A ∈ F, B ⊆ A ∧ Disjoint (A \ B) H := by
  obtain ⟨f, hf, hB, hi⟩ := h
  have hd : ∀ i j, i ≠ j → Disjoint (f i \ B) (f j \ B) := by
    intro i j hij
    apply disjoint_left.mpr
    intro a hai haj
    have hab : a ∈ B := by
      rw [← hi i j hij]
      exact mem_inter.mpr ⟨(mem_sdiff.mp hai).1, (mem_sdiff.mp haj).1⟩
    exact (mem_sdiff.mp hai).2 hab
  obtain ⟨i, hiH⟩ := exists_disjoint_of_pairwiseDisjoint (fun i => f i \ B) hd (H \ B) hH
  refine ⟨f i, hf i, hB i, disjoint_left.mpr ?_⟩
  intro a ha haH
  exact disjoint_left.mp hiH ha (mem_sdiff.mpr ⟨haH, (mem_sdiff.mp ha).2⟩)

theorem KernelWitness.inter_eq {F : Finset (Finset α)} {B H : Finset α} {t : ℕ}
    (h : KernelWitness F B t) (hH : (H \ B).card < t) :
    ∃ A ∈ F, A ∩ H = B ∩ H := by
  obtain ⟨A, hA, hBA, hd⟩ := h.avoid hH
  refine ⟨A, hA, ?_⟩
  ext a
  constructor
  · rintro ha
    have haA := (mem_inter.mp ha).1
    have haH := (mem_inter.mp ha).2
    have haB : a ∈ B := by
      by_contra hn
      exact disjoint_left.mp hd (mem_sdiff.mpr ⟨haA, hn⟩) haH
    exact mem_inter.mpr ⟨haB, haH⟩
  · intro ha
    exact mem_inter.mpr ⟨hBA (mem_inter.mp ha).1, (mem_inter.mp ha).2⟩

end Problem572
