module

public import RequestProject.Euler.RadialStationary

/-!
# Bounds for the actual circular radial profile

The circular profile is globally Lipschitz even at its two interfaces.
Its forward averages retain the value bound and have first derivatives
bounded uniformly in the averaging scale.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

lemma cellOmegaSq_eq_clippedInv (s : ℝ) :
    cellOmegaSq s = (3 / 4 : ℝ) * max ((max s (3 / 5))⁻¹ - 1) 0 := by
  let a : ℝ := max s (3 / 5)
  have ha0 : (3 / 5 : ℝ) ≤ a := le_max_right _ _
  have ha : 0 < a := by linarith
  change 3 * (1 - min a 1) / (4 * a) = (3 / 4 : ℝ) * max (a⁻¹ - 1) 0
  by_cases ha1 : a ≤ 1
  · have hi : 0 ≤ a⁻¹ - 1 := by
      rw [sub_nonneg, inv_eq_one_div]
      apply (le_div_iff₀ ha).mpr
      simpa using ha1
    rw [min_eq_left ha1, max_eq_left hi]
    field_simp
  · have ha1' : 1 ≤ a := (lt_of_not_ge ha1).le
    have hi : a⁻¹ - 1 ≤ 0 := by
      rw [sub_nonpos, inv_eq_one_div]
      apply (div_le_iff₀ ha).mpr
      simpa using ha1'
    rw [min_eq_right ha1', max_eq_right hi]
    simp

lemma lipschitz_clippedInv :
    LipschitzWith 3 (fun s : ℝ => (max s (3 / 5))⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |(max s (3 / 5))⁻¹ - (max t (3 / 5))⁻¹| ≤ 3 * |s - t|
  let a : ℝ := max s (3 / 5)
  let b : ℝ := max t (3 / 5)
  have ha0 : (3 / 5 : ℝ) ≤ a := le_max_right _ _
  have hb0 : (3 / 5 : ℝ) ≤ b := le_max_right _ _
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hab : (3 / 5 : ℝ) * (3 / 5) ≤ a * b :=
    mul_le_mul ha0 hb0 (by norm_num) ha.le
  have hmax : |b - a| ≤ |s - t| := by
    have h := ((LipschitzWith.id : LipschitzWith 1 (fun s : ℝ => s)).max_const
      (3 / 5 : ℝ)).dist_le_mul t s
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_comm, a, b, id_eq] using h
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  change |a⁻¹ - b⁻¹| ≤ _
  rw [heq, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb]
  calc
    |b - a| / (a * b) ≤ 3 * |b - a| := by
      apply (div_le_iff₀ (mul_pos ha hb)).mpr
      nlinarith [abs_nonneg (b - a)]
    _ ≤ 3 * |s - t| := mul_le_mul_of_nonneg_left hmax (by norm_num)

/-- A coarse, explicit global Lipschitz constant for the actual circular
angular profile, including the interfaces `s = 3/5` and `s = 1`. -/
lemma lipschitz_cellOmegaSq : LipschitzWith 3 cellOmegaSq := by
  have hsub : LipschitzWith 3 (fun s : ℝ => (max s (3 / 5))⁻¹ - 1) := by
    simpa using lipschitz_clippedInv.sub (LipschitzWith.const (1 : ℝ))
  have hmax := hsub.max_const 0
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |cellOmegaSq s - cellOmegaSq t| ≤ 3 * |s - t|
  rw [cellOmegaSq_eq_clippedInv, cellOmegaSq_eq_clippedInv, ← mul_sub, abs_mul]
  have h := hmax.dist_le_mul s t
  change |max ((max s (3 / 5))⁻¹ - 1) 0 - max ((max t (3 / 5))⁻¹ - 1) 0| ≤ 3 * |s - t| at h
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  nlinarith [abs_nonneg (s - t)]

lemma cellOmegaSq_nonneg (s : ℝ) : 0 ≤ cellOmegaSq s := by
  rw [cellOmegaSq_eq_clippedInv]
  positivity

lemma cellOmegaSq_le_half (s : ℝ) : cellOmegaSq s ≤ 1 / 2 := by
  let a : ℝ := max s (3 / 5)
  have ha0 : (3 / 5 : ℝ) ≤ a := le_max_right _ _
  have ha : 0 < a := by linarith
  change 3 * (1 - min a 1) / (4 * a) ≤ 1 / 2
  apply (div_le_iff₀ (show 0 < 4 * a by positivity)).mpr
  by_cases ha1 : a ≤ 1
  · rw [min_eq_left ha1]
    nlinarith
  · rw [min_eq_right (lt_of_not_ge ha1).le]
    nlinarith

lemma norm_cellOmegaSq_le_half (s : ℝ) : ‖cellOmegaSq s‖ ≤ 1 / 2 := by
  rw [Real.norm_of_nonneg (cellOmegaSq_nonneg s)]
  exact cellOmegaSq_le_half s

/-- The derivative of the forward average is the difference quotient of
its original continuous profile. -/
lemma deriv_profileAverage {f : ℝ → ℝ} (hf : Continuous f) (ε s : ℝ) :
    deriv (profileAverage f ε) s = ε⁻¹ * (f (s + ε) - f s) := by
  have hr := (hasDerivAt_profilePrimitive hf (s + ε)).comp s ((hasDerivAt_id s).add_const ε)
  have hd := (hr.sub (hasDerivAt_profilePrimitive hf s)).const_mul ε⁻¹
  have h := hd.deriv
  unfold profileAverage
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one] using h

/-- A Lipschitz bound on the original profile uniformly bounds the
classical derivatives of all its positive-scale forward averages. -/
lemma norm_deriv_profileAverage_le {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : ‖deriv (profileAverage f ε) s‖ ≤ K := by
  rw [deriv_profileAverage hf.continuous, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have h : ‖f (s + ε) - f s‖ ≤ (K : ℝ) * ε := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hε] using
      hf.dist_le_mul (s + ε) s
  calc
    ε⁻¹ * ‖f (s + ε) - f s‖ ≤ ε⁻¹ * ((K : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hε.le)
    _ = K := by field_simp

lemma norm_profileAverage_cellOmegaSq_le_half {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : 0 ≤ s) : ‖profileAverage cellOmegaSq ε s‖ ≤ 1 / 2 :=
  norm_profileAverage_le continuous_cellOmegaSq (fun s _ => norm_cellOmegaSq_le_half s) hε hs

lemma norm_deriv_profileAverage_cellOmegaSq_le_three {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ‖deriv (profileAverage cellOmegaSq ε) s‖ ≤ 3 :=
  norm_deriv_profileAverage_le lipschitz_cellOmegaSq hε s

end Euler2D

end
