module

public import RequestProject.Euler.PlanarKernelL1
public import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative bounds and cancellation of the actual local kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff

namespace Euler2D

lemma planar_norm_perpJ (x : R2) : ‖perpJ x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, perpJ, Fin.sum_univ_two, add_comm]

lemma planar_kernelK_neg (x : R2) : kernelK (-x) = -kernelK x := by
  have hJ : perpJ (-x) = -perpJ x := by
    ext i
    fin_cases i <;> simp [perpJ]
  simp only [kernelK, norm_neg, hJ, smul_neg]

lemma cutoffKernelK_neg (χ : ℝ → ℝ) (x : R2) :
    cutoffKernelK χ (-x) = -cutoffKernelK χ x := by
  simp only [cutoffKernelK, radialKernelCutoff, norm_neg, planar_kernelK_neg, smul_neg]

lemma localPlanarKernel_neg (x : R2) : localPlanarKernel (-x) = -localPlanarKernel x :=
  cutoffKernelK_neg planarCutoff x

lemma integral_localPlanarKernel : (∫ x, localPlanarKernel x) = 0 := by
  have he : (∫ x, localPlanarKernel x) = -(∫ x, localPlanarKernel x) := by
    calc
      _ = ∫ x, localPlanarKernel (-x) := (integral_neg_eq_self _ volume).symm
      _ = -(∫ x, localPlanarKernel x) := by
        simp_rw [localPlanarKernel_neg]
        exact integral_neg _
  have hz : (2 : ℝ) • (∫ x, localPlanarKernel x) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

lemma localPlanarKernel_eq_kernelK_of_norm_le_half {x : R2} (hx : ‖x‖ ≤ 1 / 2) :
    localPlanarKernel x = kernelK x := by
  have hs : |‖x‖ ^ 2| ≤ 1 / 4 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg x]
  change planarCutoff (‖x‖ ^ 2) • kernelK x = kernelK x
  rw [planarCutoff_eq_one hs, one_smul]

lemma norm_planar_kernelK (x : R2) : ‖kernelK x‖ = (2 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [kernelK, perpJ]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [kernelK, norm_smul, Real.norm_of_nonneg (by positivity), planar_norm_perpJ]
    field_simp

lemma norm_localPlanarKernel_le (x : R2) :
    ‖localPlanarKernel x‖ ≤ (2 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
  change ‖planarCutoff (‖x‖ ^ 2) • kernelK x‖ ≤ _
  have hc : 0 ≤ planarCutoff (‖x‖ ^ 2) := planarCutoffBump.nonneg
  have hc1 : planarCutoff (‖x‖ ^ 2) ≤ 1 := planarCutoffBump.le_one
  rw [norm_smul, Real.norm_of_nonneg hc]
  calc
    _ ≤ 1 * ‖kernelK x‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_planar_kernelK]

lemma hasFDerivAt_cutoffKernelK {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {x : R2} (hx : x ≠ 0) :
    HasFDerivAt (cutoffKernelK χ)
      (χ (‖x‖ ^ 2) • gradKernel x +
        (deriv χ (‖x‖ ^ 2) • (2 • innerSL ℝ x)).smulRight (kernelK x)) x := by
  have hc : HasFDerivAt (radialKernelCutoff χ)
      (deriv χ (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
    (hχ.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  exact hc.smul (hasFDerivAt_kernelK hx)

lemma fderiv_cutoffKernelK {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {x : R2} (hx : x ≠ 0) :
    fderiv ℝ (cutoffKernelK χ) x =
      χ (‖x‖ ^ 2) • gradKernel x +
        (deriv χ (‖x‖ ^ 2) • (2 • innerSL ℝ x)).smulRight (kernelK x) :=
  (hasFDerivAt_cutoffKernelK hχ hx).fderiv

lemma norm_fderiv_localPlanarKernel_le_of_norm_le_one {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |deriv planarCutoff s| ≤ D)
    {x : R2} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ‖fderiv ℝ localPlanarKernel x‖ ≤
      ((3 + 2 * D) / (2 * Real.pi)) * (‖x‖ ^ 2)⁻¹ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : ‖x‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  have hd := hbound _ hs
  change ‖fderiv ℝ (cutoffKernelK planarCutoff) x‖ ≤ _
  rw [fderiv_cutoffKernelK (contDiff_planarCutoff.of_le (by simp)) hx]
  have hfirst : ‖planarCutoff (‖x‖ ^ 2) • gradKernel x‖ ≤
      3 / (2 * Real.pi) * (‖x‖ ^ 2)⁻¹ := by
    have hc : 0 ≤ planarCutoff (‖x‖ ^ 2) := planarCutoffBump.nonneg
    have hc1 : planarCutoff (‖x‖ ^ 2) ≤ 1 := planarCutoffBump.le_one
    rw [norm_smul, Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_gradKernel_le x)
  have hsecond : ‖(deriv planarCutoff (‖x‖ ^ 2) • (2 • innerSL ℝ x)).smulRight
      (kernelK x)‖ ≤ D / Real.pi := by
    rw [show (2 : ℕ) • innerSL ℝ x = (2 : ℝ) • innerSL ℝ x by simp only [two_smul]]
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
      Real.norm_eq_abs, innerSL_apply_norm, norm_planar_kernelK]
    norm_num only [Real.norm_ofNat]
    calc
      |deriv planarCutoff (‖x‖ ^ 2)| * (2 * ‖x‖) *
          ((2 * Real.pi)⁻¹ * ‖x‖⁻¹) ≤
        D * (2 * ‖x‖) * ((2 * Real.pi)⁻¹ * ‖x‖⁻¹) := by gcongr
      _ = D / Real.pi := by field_simp
  have hInv : 1 ≤ (‖x‖ ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hn)).mpr hs.2
  calc
    _ ≤ ‖planarCutoff (‖x‖ ^ 2) • gradKernel x‖ +
        ‖(deriv planarCutoff (‖x‖ ^ 2) • (2 • innerSL ℝ x)).smulRight (kernelK x)‖ :=
      norm_add_le _ _
    _ ≤ 3 / (2 * Real.pi) * (‖x‖ ^ 2)⁻¹ + D / Real.pi := add_le_add hfirst hsecond
    _ ≤ 3 / (2 * Real.pi) * (‖x‖ ^ 2)⁻¹ + D / Real.pi * (‖x‖ ^ 2)⁻¹ := by
      gcongr
      exact le_mul_of_one_le_right (div_nonneg hD Real.pi_pos.le) hInv
    _ = _ := by ring

lemma fderiv_localPlanarKernel_eq_zero_of_one_lt_norm {x : R2} (hx : 1 < ‖x‖) :
    fderiv ℝ localPlanarKernel x = 0 := by
  have he : localPlanarKernel =ᶠ[𝓝 x] fun _ => (0 : R2) := by
    filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with y hy
    exact localPlanarKernel_eq_zero_of_one_le_norm hy.le
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : R2) x).fderiv

/-- The actual cutoff kernel has the Calderón--Zygmund first derivative
bound with a finite constant determined by the fixed smooth cutoff. -/
theorem exists_norm_fderiv_localPlanarKernel_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R2, x ≠ 0 →
      ‖fderiv ℝ localPlanarKernel x‖ ≤ C * (‖x‖ ^ 2)⁻¹ := by
  have hd : Continuous (deriv planarCutoff) :=
    (contDiff_infty_iff_deriv.mp contDiff_planarCutoff).2.continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hd.continuousOn
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨(3 + 2 * D) / (2 * Real.pi), by positivity, fun x hx => ?_⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · have hbound : ∀ s ∈ Icc (0 : ℝ) 1, |deriv planarCutoff s| ≤ D := by
      intro s hs
      have hb : |deriv planarCutoff s| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB s hs
      exact hb.trans (le_max_left _ _)
    exact norm_fderiv_localPlanarKernel_le_of_norm_le_one hD hbound hx hx1
  · rw [fderiv_localPlanarKernel_eq_zero_of_one_lt_norm (lt_of_not_ge hx1), norm_zero]
    positivity

lemma localPlanarKernel_eventuallyEq_kernelK :
    localPlanarKernel =ᶠ[𝓝 (0 : R2)] kernelK := by
  filter_upwards [Metric.ball_mem_nhds (0 : R2) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  have hxn : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx
  exact localPlanarKernel_eq_kernelK_of_norm_le_half hxn.le

lemma fderiv_localPlanarKernel_eq_gradKernel {x : R2} (hx : x ≠ 0)
    (hr : ‖x‖ < 1 / 2) : fderiv ℝ localPlanarKernel x = gradKernel x := by
  have he : localPlanarKernel =ᶠ[𝓝 x] kernelK := by
    filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds hr)] with y hy
    exact localPlanarKernel_eq_kernelK_of_norm_le_half hy.le
  exact he.fderiv_eq.trans (hasFDerivAt_kernelK hx).fderiv

/-- Away from the diagonal, the derivative bound gives the actual
kernel difference estimate used in the near/far convolution split. -/
theorem norm_localPlanarKernel_sub_le {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 →
      ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    {x y : R2} (hx : x ≠ 0) (hxy : ‖y - x‖ ≤ ‖x‖ / 2) :
    ‖localPlanarKernel y - localPlanarKernel x‖ ≤
      (4 * C * (‖x‖ ^ 2)⁻¹) * ‖y - x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlower (z : R2) (hz : z ∈ closedBall x (‖x‖ / 2)) : ‖x‖ / 2 ≤ ‖z‖ := by
    have hd : ‖z - x‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have ht := norm_sub_norm_le x z
    rw [norm_sub_rev] at ht
    linarith
  have hdiff : ∀ z ∈ closedBall x (‖x‖ / 2), DifferentiableAt ℝ localPlanarKernel z := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < ‖x‖ / 2) (hlower z hz))
    exact (contDiffAt_localPlanarKernel hz0).differentiableAt (by simp)
  have hbound : ∀ z ∈ closedBall x (‖x‖ / 2),
      ‖fderiv ℝ localPlanarKernel z‖ ≤ 4 * C * (‖x‖ ^ 2)⁻¹ := by
    intro z hz
    have hzlower := hlower z hz
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < ‖x‖ / 2) hzlower
    have hratio : (‖z‖ ^ 2)⁻¹ ≤ 4 * (‖x‖ ^ 2)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (sq_pos_of_pos hzn) (sq_pos_of_pos hn)).mpr
      nlinarith
    calc
      _ ≤ C * (‖z‖ ^ 2)⁻¹ := hderiv z (norm_pos_iff.mp hzn)
      _ ≤ C * (4 * (‖x‖ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hratio hC
      _ = _ := by ring
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall x _) (mem_closedBall_self (by positivity))
    (by simpa only [mem_closedBall, dist_eq_norm] using hxy)

end Euler2D

end
