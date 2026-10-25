module

public import Mathlib

/-! Actual geometric Banach series give quantitative limits of
telescoping orbit coefficients, including the full tail error. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem summable_of_norm_le_geometric {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ C * q ^ n) : Summable v := by
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  exact ((summable_geometric_of_norm_lt_one hq).mul_left C).of_norm_bounded hv

theorem norm_tsum_le_geometric {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ C * q ^ n) : ‖∑' n : ℕ, v n‖ ≤ C / (1 - q) := by
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  calc
    _ ≤ ∑' n : ℕ, C * q ^ n :=
      tsum_of_norm_bounded ((summable_geometric_of_norm_lt_one hq).mul_left C).hasSum hv
    _ = C / (1 - q) := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq, div_eq_mul_inv]

theorem norm_tsum_nat_add_le_geometric {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ C * q ^ n) (n : ℕ) :
    ‖∑' k : ℕ, v (k + n)‖ ≤ (C / (1 - q)) * q ^ n := by
  have hbound (k : ℕ) : ‖v (k + n)‖ ≤ (C * q ^ n) * q ^ k := by
    calc
      _ ≤ C * q ^ (k + n) := hv _
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ (C * q ^ n) / (1 - q) := norm_tsum_le_geometric hq0 hq1 hbound
    _ = _ := by ring

theorem exists_limit_of_geometric_increments {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {v w : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ C * q ^ n)
    (hw : ∀ n, w (n + 1) = w n - v n) :
    ∃ c : E, Tendsto w atTop (𝓝 c) ∧
      (∀ n, ‖w n - c‖ ≤ (C / (1 - q)) * q ^ n) ∧ ‖c - w 0‖ ≤ C / (1 - q) := by
  have hs := summable_of_norm_le_geometric hq0 hq1 hv
  let c := w 0 - ∑' n : ℕ, v n
  have hfinite (n : ℕ) : w n = w 0 - ∑ k ∈ Finset.range n, v k := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    | succ n ih => rw [hw, ih, Finset.sum_range_succ]; abel
  have hlim : Tendsto w atTop (𝓝 c) := by
    have h : Tendsto (fun n : ℕ => w 0 - ∑ k ∈ Finset.range n, v k) atTop (𝓝 c) :=
      tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
    exact h.congr' (Filter.Eventually.of_forall (fun n => (hfinite n).symm))
  have herr (n : ℕ) : ‖w n - c‖ ≤ (C / (1 - q)) * q ^ n := by
    have htail := Summable.sum_add_tsum_nat_add n hs
    have he : w n - c = ∑' k : ℕ, v (k + n) := by
      dsimp only [c]
      rw [hfinite, ← htail]
      abel
    rw [he]
    exact norm_tsum_nat_add_le_geometric hq0 hq1 hv n
  refine ⟨c, hlim, herr, ?_⟩
  have h := herr 0
  simpa only [pow_zero, mul_one, norm_sub_rev] using h

end Euler2D

end
