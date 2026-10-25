module

public import RequestProject.Euler.ContourFourierSmoothingMultiplier
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.PSeries

/-! Actual exponentially decaying integer symbols define bounded
Fourier operators on the original little C¹ Hölder space. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) geometricLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) geometricLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem summable_contourFourierModeWeight_geometric (γ : ℝ≥0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => contourFourierModeWeight γ n * r ^ n.natAbs) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hs : Summable (fun n : ℕ =>
      (1 + (n : ℝ) + (n : ℝ) ^ 2 * Real.pi ^ (1 - (γ : ℝ))) * r ^ n) := by
    convert (hs0.add hs1).add (hs2.mul_left (Real.pi ^ (1 - (γ : ℝ)))) using 1
    funext n
    ring
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [contourFourierModeWeight, Int.cast_natCast, norm_natCast,
      Int.natAbs_natCast] using hs
  · simpa only [contourFourierModeWeight, Int.cast_neg, Int.cast_natCast, norm_neg,
      norm_natCast, Int.natAbs_neg, Int.natAbs_natCast] using hs

theorem summable_contourFourierModeWeight_of_geometric_bound (γ : ℝ≥0)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    {c : ℤ → ℂ} (hc : ∀ n, ‖c n‖ ≤ C * r ^ n.natAbs) :
    Summable (fun n => contourFourierModeWeight γ n * ‖c n‖) := by
  apply ((summable_contourFourierModeWeight_geometric γ hr0 hr1).mul_left C).of_nonneg_of_le
    (fun n => mul_nonneg (contourFourierModeWeight_nonneg γ n) (norm_nonneg _))
  intro n
  calc
    _ ≤ contourFourierModeWeight γ n * (C * r ^ n.natAbs) :=
      mul_le_mul_of_nonneg_left (hc n) (contourFourierModeWeight_nonneg γ n)
    _ = _ := by ring

theorem norm_littleContourFourierMultiplierCLM_le_of_geometric_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r C : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    {c : ℤ → ℂ} (hc : ∀ n, ‖c n‖ ≤ C * r ^ n.natAbs) :
    ‖littleContourFourierMultiplierCLM hγ hγ1 c‖ ≤
      C * ∑' n : ℤ, contourFourierModeWeight γ n * r ^ n.natAbs := by
  have hs := summable_contourFourierModeWeight_of_geometric_bound γ hr0 hr1 hC hc
  have ht := (summable_contourFourierModeWeight_geometric γ hr0 hr1).mul_left C
  calc
    _ ≤ ∑' n : ℤ, contourFourierModeWeight γ n * ‖c n‖ :=
      norm_littleContourFourierMultiplierCLM_le hγ hγ1 hs
    _ ≤ ∑' n : ℤ, C * (contourFourierModeWeight γ n * r ^ n.natAbs) := by
      apply hs.tsum_le_tsum _ ht
      intro n
      calc
        _ ≤ contourFourierModeWeight γ n * (C * r ^ n.natAbs) :=
          mul_le_mul_of_nonneg_left (hc n) (contourFourierModeWeight_nonneg γ n)
        _ = _ := by ring
    _ = _ := tsum_mul_left

end Euler2D

end
