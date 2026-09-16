import Problem572.Basic

namespace Problem572

open Finset

def growthThreshold (c d : ℕ) : ℕ :=
  4 * (c * 8 ^ d * (d + 1).factorial + d + 5)

theorem pow_lt_half_choose (c d n : ℕ) (hn : growthThreshold c d ≤ n) :
    c * n ^ d < (n / 2 - 3).choose (d + 1) := by
  let q := n / 4
  have hq : c * 8 ^ d * (d + 1).factorial < q := by
    dsimp [growthThreshold] at hn
    dsimp [q]
    omega
  have hqpos : 0 < q := by omega
  have hnq : n ≤ 8 * q := by
    dsimp [growthThreshold] at hn
    dsimp [q]
    omega
  have hbase : q ≤ (n / 2 - 3) + 1 - (d + 1) := by
    dsimp [growthThreshold] at hn
    dsimp [q]
    omega
  have hlower : q ^ (d + 1) ≤ (d + 1).factorial * (n / 2 - 3).choose (d + 1) := by
    calc
      q ^ (d + 1) ≤ ((n / 2 - 3) + 1 - (d + 1)) ^ (d + 1) := Nat.pow_le_pow_left hbase _
      _ ≤ (n / 2 - 3).descFactorial (d + 1) := Nat.pow_sub_le_descFactorial _ _
      _ = _ := Nat.descFactorial_eq_factorial_mul_choose _ _
  have hupper : (d + 1).factorial * (c * n ^ d) < q ^ (d + 1) := by
    calc
      (d + 1).factorial * (c * n ^ d) ≤
          (d + 1).factorial * (c * (8 * q) ^ d) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnq _))
      _ = (c * 8 ^ d * (d + 1).factorial) * q ^ d := by rw [mul_pow]; ring
      _ < q * q ^ d := Nat.mul_lt_mul_of_pos_right hq (pow_pos hqpos _)
      _ = q ^ (d + 1) := by ring
  exact Nat.lt_of_mul_lt_mul_left (hupper.trans_le hlower)

theorem choose_superadditive (a b r : ℕ) (hr : 0 < r) :
    a.choose r + b.choose r ≤ (a + b).choose r := by
  rw [Nat.add_choose_eq]
  have hsub : ({(r, 0), (0, r)} : Finset (ℕ × ℕ)) ⊆ Finset.antidiagonal r := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · simp
    · obtain rfl := mem_singleton.mp hp
      simp
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Nat.zero_le (a.choose p.1 * b.choose p.2))
  simpa [show r ≠ 0 by omega] using hle

theorem small_block_choose_gap {c d n m : ℕ}
    (hn : growthThreshold c d ≤ n) (hm : 2 * m ≤ n) :
    (m - 3).choose (d + 1) + c * n ^ d < (n - 3).choose (d + 1) := by
  have hnlarge : 20 ≤ n := by unfold growthThreshold at hn; omega
  calc
    (m - 3).choose (d + 1) + c * n ^ d <
        (m - 3).choose (d + 1) + (n / 2 - 3).choose (d + 1) :=
      Nat.add_lt_add_left (pow_lt_half_choose c d n hn) _
    _ ≤ ((m - 3) + (n / 2 - 3)).choose (d + 1) := choose_superadditive _ _ _ (by omega)
    _ ≤ (n - 3).choose (d + 1) := Nat.choose_le_choose _ (by omega)

theorem pair_residual_degree_lt {k n g : ℕ} (hk : 4 ≤ k) (hn : k < n)
    (hg : g * (k - 2) ≤ (n - 2) * (n - 4).choose (k - 4)) :
    g < (n - 3).choose (k - 3) := by
  have hc : 0 < (n - 4).choose (k - 4) := Nat.choose_pos (by omega)
  have he : (n - 3) * (n - 4).choose (k - 4) =
      (k - 3) * (n - 3).choose (k - 3) := by
    have hh := Nat.succ_mul_choose_eq (n - 4) (k - 4)
    have hs1 : (n - 4).succ = n - 3 := by omega
    have hs2 : (k - 4).succ = k - 3 := by omega
    simpa only [hs1, hs2, Nat.mul_comm] using hh
  have hbc : (n - 4).choose (k - 4) < (n - 3).choose (k - 3) := by
    apply lt_of_not_ge
    intro hle
    have hh := Nat.mul_le_mul_left (k - 3) hle
    have hh' : (k - 3) < n - 3 := by omega
    have hlt := Nat.mul_lt_mul_of_pos_right hh' hc
    omega
  have hs1 : n - 2 = (n - 3) + 1 := by omega
  have hs2 : k - 2 = (k - 3) + 1 := by omega
  have hh : (n - 2) * (n - 4).choose (k - 4) <
      (k - 2) * (n - 3).choose (k - 3) := by
    rw [hs1, hs2, Nat.add_mul, Nat.add_mul, he]
    simpa using hbc
  exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_comm] using hg.trans_lt hh)

end Problem572
