module

public import Mathlib

/-! The finite weighted source estimates behind the capture induction.
The terminal exponential envelope is an explicit finite-interval bound. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open scoped BigOperators

namespace Euler2D

theorem capture_weighted_square_budget {b : ℕ → ℝ} {lam M a D : ℝ}
    (hLam : 1 < lam) (hM : 0 ≤ M) (ha : 0 ≤ a) {N : ℕ}
    (hb0 : ∀ j < N, 0 ≤ b j)
    (hb : ∀ j < N, b j ≤ M * a * lam ^ j)
    (hterminal : a * lam ^ N ≤ D) :
    ∑ j ∈ Finset.range N, (b j) ^ 2 / lam ^ (j + 1) ≤ M ^ 2 * a * D / (lam - 1) := by
  have hl0 : 0 < lam := zero_lt_one.trans hLam
  have hp : 0 < lam - 1 := sub_pos.mpr hLam
  have hcoef : 0 ≤ M ^ 2 * a ^ 2 := by positivity
  have hpoint : ∀ j < N, (b j) ^ 2 / lam ^ (j + 1) ≤ M ^ 2 * a ^ 2 * lam ^ j := by
    intro j hj
    calc
      _ ≤ (M * a * lam ^ j) ^ 2 / lam ^ (j + 1) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (hb0 j hj) (hb j hj) 2)
          (pow_nonneg hl0.le _)
      _ = (M ^ 2 * a ^ 2 / lam) * lam ^ j := by
        rw [pow_succ]
        field_simp
        <;> ring
      _ ≤ M ^ 2 * a ^ 2 * lam ^ j := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hl0.le _)
        apply (div_le_iff₀ hl0).mpr
        nlinarith only [mul_nonneg hcoef (sub_nonneg.mpr hLam.le)]
  have hsum : ∑ j ∈ Finset.range N, lam ^ j ≤ lam ^ N / (lam - 1) := by
    rw [geom_sum_eq hLam.ne' N]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  calc
    _ ≤ ∑ j ∈ Finset.range N, M ^ 2 * a ^ 2 * lam ^ j :=
      Finset.sum_le_sum (fun j hj => hpoint j (Finset.mem_range.mp hj))
    _ = (M ^ 2 * a ^ 2) * ∑ j ∈ Finset.range N, lam ^ j := by rw [Finset.mul_sum]
    _ ≤ (M ^ 2 * a ^ 2) * (lam ^ N / (lam - 1)) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = M ^ 2 * a * (a * lam ^ N) / (lam - 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hterminal (by positivity)) hp.le

theorem capture_weighted_linear_budget {b : ℕ → ℝ} {lam M a : ℝ}
    (hLam : 1 < lam) (hM : 0 ≤ M) (ha : 0 ≤ a) {N : ℕ}
    (hb : ∀ j < N, b j ≤ M * a * lam ^ j) :
    ∑ j ∈ Finset.range N, b j / lam ^ (j + 1) ≤ (N : ℝ) * M * a := by
  have hl0 : 0 < lam := zero_lt_one.trans hLam
  have hpoint : ∀ j < N, b j / lam ^ (j + 1) ≤ M * a := by
    intro j hj
    calc
      _ ≤ (M * a * lam ^ j) / lam ^ (j + 1) :=
        div_le_div_of_nonneg_right (hb j hj) (pow_nonneg hl0.le _)
      _ = M * a / lam := by
        rw [pow_succ]
        field_simp
      _ ≤ _ := (div_le_iff₀ hl0).mpr (by
        nlinarith only [mul_nonneg (mul_nonneg hM ha) (sub_nonneg.mpr hLam.le)])
  calc
    _ ≤ ∑ j ∈ Finset.range N, M * a :=
      Finset.sum_le_sum (fun j hj => hpoint j (Finset.mem_range.mp hj))
    _ = _ := by simp; ring

theorem capture_weighted_nonlinear_forcing_budget {b f : ℕ → ℝ}
    {lam M a D C κ F : ℝ} (hLam : 1 < lam) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) {N : ℕ}
    (hb0 : ∀ j < N, 0 ≤ b j) (hb : ∀ j < N, b j ≤ M * a * lam ^ j)
    (hterminal : a * lam ^ N ≤ D)
    (hf : ∑ j ∈ Finset.range N, f j / lam ^ (j + 1) ≤ F) :
    ∑ j ∈ Finset.range N, (C * (b j) ^ 2 + f j + κ * b j) / lam ^ (j + 1) ≤
      C * (M ^ 2 * a * D / (lam - 1)) + F + κ * ((N : ℝ) * M * a) := by
  have hs := capture_weighted_square_budget hLam hM ha hb0 hb hterminal
  have hl := capture_weighted_linear_budget hLam hM ha hb
  have he : (∑ j ∈ Finset.range N, (C * (b j) ^ 2 + f j + κ * b j) / lam ^ (j + 1)) =
      C * (∑ j ∈ Finset.range N, (b j) ^ 2 / lam ^ (j + 1)) +
        (∑ j ∈ Finset.range N, f j / lam ^ (j + 1)) +
        κ * (∑ j ∈ Finset.range N, b j / lam ^ (j + 1)) := by
    simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [he]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs hC) hf)
    (mul_le_mul_of_nonneg_left hl hκ)

end Euler2D

end
