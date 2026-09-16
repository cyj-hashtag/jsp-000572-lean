import Problem572.Counting

/-!
# The deletion argument

Each deletion removes at most two points and raises the integer excess by at
least one. Hence |X| + 2 * excess cannot decrease. This is the finite descent
in the proof of Frankl's Theorem 2, without an equality classification.
-/

namespace Problem572

open Finset

variable {α : Type*} [DecidableEq α]

def extremalBound (k n : ℕ) : ℕ := (n - 2).choose (k - 2)

def excess (k : ℕ) (X : Finset α) (F : Finset (Finset α)) : ℕ :=
  F.card - extremalBound k X.card

def LocalReduction (k N : ℕ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (F : Finset (Finset α)),
    Supported X F → Uniform k F → NoSingletonIntersections F →
    N < X.card → extremalBound k X.card < F.card →
    ∃ Y : Finset α, Y ⊆ X ∧ Y.card < X.card ∧ X.card ≤ Y.card + 2 ∧
      excess k X F + 1 ≤ excess k Y (restrict F Y)

theorem descent_potential_bound {k N : ℕ} (hr : LocalReduction k N α)
    (X : Finset α) (F : Finset (Finset α))
    (hX : Supported X F) (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (he : extremalBound k X.card < F.card) :
    X.card + 2 * excess k X F ≤ N + 2 * N.choose k := by
  generalize hn : X.card = n at *
  induction n using Nat.strong_induction_on generalizing X F with
  | h n ih =>
    by_cases hsmall : n ≤ N
    · have hc := (uniform_card_le hU hX).trans
        (Nat.choose_le_choose (a := X.card) (b := N) k (by omega))
      have hsub : excess k X F ≤ F.card := Nat.sub_le _ _
      omega
    · obtain ⟨Y, hYX, hYlt, hYsize, heY⟩ := hr X F hX hU hF (by omega) (by simpa [hn] using he)
      have hsub : restrict F Y ⊆ F := filter_subset _ _
      have hYX' : Supported Y (restrict F Y) := fun A hA => (mem_restrict.mp hA).2
      have hpos : extremalBound k Y.card < (restrict F Y).card := by
        unfold excess at heY
        omega
      have hi := ih Y.card (by omega) Y (restrict F Y) hYX'
        (hU.mono hsub) (hF.mono hsub) rfl hpos
      omega

theorem card_le_of_localReduction {k N : ℕ} (hr : LocalReduction k N α)
    (X : Finset α) (F : Finset (Finset α))
    (hX : Supported X F) (hU : Uniform k F) (hF : NoSingletonIntersections F)
    (hn : N + 2 * N.choose k < X.card) : F.card ≤ extremalBound k X.card := by
  by_contra! he
  have hp := descent_potential_bound hr X F hX hU hF he
  omega

theorem exists_intersection_of_localReduction {k N : ℕ} (hr : LocalReduction k N α)
    (hk : 4 ≤ k) (X : Finset α) (F : Finset (Finset α))
    (hX : Supported X F) (hU : Uniform k F)
    (hn : N + 2 * N.choose k < X.card) (he : extremalBound k X.card < F.card) :
    ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ (A ∩ B).card = 1 := by
  by_contra! h
  have hF : NoSingletonIntersections F := by
    intro A hA B hB hc
    by_cases hab : A = B
    · subst B
      rw [inter_self, hU A hA] at hc
      omega
    · exact h A hA B hB hab hc
  exact (not_lt_of_ge (card_le_of_localReduction hr X F hX hU hF hn)) he

end Problem572
