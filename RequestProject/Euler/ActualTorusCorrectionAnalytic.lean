module

public import RequestProject.Euler.ActualTorusKernelCancellation
public import RequestProject.Euler.ExteriorContourForcing

/-! The true zero-circulation periodic correction is antiholomorphic
after the genuine quadratic Green term cancels. This identity uses
the actual Fourier-constructed torus correction kernel. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem actualComplexHarmonicRemainder_smooth : ContDiff ℝ ∞ actualComplexHarmonicRemainder :=
  torusGreenHarmonicRemainder_smooth.comp complexTorusPoint_smooth

theorem complexPerpGradientOperator_normSq (z : ℂ) :
    complexPerpGradientOperator (fderiv ℝ (fun x : ℂ => ‖x‖ ^ 2) z) = 2 * I * z := by
  rw [complexPerpGradientOperator_apply, fderiv_norm_sq_apply]
  apply Complex.ext <;>
    simp [ContinuousLinearMap.smul_apply, innerSL_apply, Complex.inner, smul_eq_mul] <;> ring

theorem actualComplexRemainderKernel_eq_harmonic (z : ℂ) :
    actualComplexRemainderKernel z =
      (-((4 * (2 * Real.pi) ^ 2)⁻¹) : ℝ) • (2 * I * z) +
        I * conj (cpartial actualComplexHarmonicRemainder z) := by
  let c : ℝ := -((4 * (2 * Real.pi) ^ 2)⁻¹)
  have hH := (actualComplexHarmonicRemainder_smooth.differentiable (by simp) z).hasFDerivAt
  have hG := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul c).add hH
  have he : (fun x : ℂ => c * ‖x‖ ^ 2 + actualComplexHarmonicRemainder x) =
      actualComplexGreenCorrection := funext (fun x =>
        (actualComplexGreenCorrection_eq_quadratic_add_harmonic x).symm)
  change HasFDerivAt (fun x : ℂ => c * ‖x‖ ^ 2 + actualComplexHarmonicRemainder x) _ z at hG
  rw [he] at hG
  have hn : complexPerpGradientOperator (2 • innerSL ℝ z) = 2 * I * z := by
    simpa only [fderiv_norm_sq_apply] using complexPerpGradientOperator_normSq z
  rw [actualComplexRemainderKernel_eq_operator, hG.fderiv, map_add, map_smul,
    hn, complexPerpGradientOperator_eq_cpartial]

def actualTorusCorrectionVelocity (w : ℂ → ℝ) (x : ℂ) : ℂ :=
  ∫ y, w y • actualComplexRemainderKernel (x - y)

theorem actualTorusCorrectionVelocity_eq_harmonic
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) {w : ℂ → ℝ}
    (hw : Integrable w) (hsupp : ∀ y, a < ‖y‖ → w y = 0)
    (hmass : ∫ y, w y = 0) (hsym : ∀ y, w (I * y) = w y)
    {x : ℂ} (hx : ‖x‖ < 3 * a) :
    actualTorusCorrectionVelocity w x =
      I * conj (cconv w (cpartial actualComplexHarmonicRemainder) x) := by
  let c : ℝ := -((4 * (2 * Real.pi) ^ 2)⁻¹)
  have hM1 : (∫ y, (w y : ℂ) * y) = 0 := by
    simpa only [momentM, pow_one] using momentM_eq_zero_of_lt_four hmass hsym (k := 1) (by norm_num)
  have hI1 : Integrable (fun y => (w y : ℂ) * y) := by
    simpa only [pow_one] using integrable_mul_pow_of_supp hw hsupp 1
  have hwo : Integrable (fun y : ℂ => (w y : ℂ)) := hw.ofReal
  have hlin : Integrable (fun y => (w y : ℂ) * (x - y)) := by
    simpa only [mul_sub] using (hwo.mul_const x).sub hI1
  have hlinzero : (∫ y, (w y : ℂ) * (x - y)) = 0 := by
    simp_rw [mul_sub]
    rw [integral_sub (hwo.mul_const x) hI1, integral_mul_const, integral_complex_ofReal,
      hmass, hM1]
    simp
  have hcp : DifferentiableOn ℂ (cpartial actualComplexHarmonicRemainder) (ball 0 (8 * a)) := by
    intro z hz
    exact (HarmonicAt.differentiableAt_complex_partial
      (harmonicOnNhd_actualComplexHarmonicRemainder z (by
        rw [mem_ball_zero_iff] at hz ⊢; linarith))).differentiableWithinAt
  have hcont : ContinuousOn (cpartial actualComplexHarmonicRemainder) (closedBall 0 (4 * a)) :=
    hcp.continuousOn.mono (closedBall_subset_ball (by linarith))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (4 * a)).exists_bound_of_continuousOn hcont
  have hcint : Integrable (fun y => (w y : ℂ) * cpartial actualComplexHarmonicRemainder (x - y)) :=
    integrable_cconv hw hsupp hcont hB (show ‖x‖ + a ≤ 4 * a by linarith)
  have hcconj : Integrable (fun y => conj ((w y : ℂ) * cpartial actualComplexHarmonicRemainder (x - y))) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hcint
  have he (y : ℂ) : w y • actualComplexRemainderKernel (x - y) =
      ((c : ℂ) * 2 * I) * ((w y : ℂ) * (x - y)) +
        I * conj ((w y : ℂ) * cpartial actualComplexHarmonicRemainder (x - y)) := by
    rw [actualComplexRemainderKernel_eq_harmonic]
    simp only [Complex.real_smul, map_mul, conj_ofReal]
    change (w y : ℂ) * ((c : ℂ) * (2 * I * (x - y)) +
      I * conj (cpartial actualComplexHarmonicRemainder (x - y))) = _
    ring
  unfold actualTorusCorrectionVelocity
  rw [integral_congr_ae (ae_of_all _ he), integral_add (hlin.const_mul _) (hcconj.const_mul _),
    integral_const_mul, hlinzero, mul_zero, zero_add, integral_const_mul, integral_conj]
  rfl

theorem analyticOnNhd_conj_actualTorusCorrectionVelocity
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) {w : ℂ → ℝ}
    (hw : Integrable w) (hsupp : ∀ y, a < ‖y‖ → w y = 0)
    (hmass : ∫ y, w y = 0) (hsym : ∀ y, w (I * y) = w y) :
    AnalyticOnNhd ℂ (fun x => conj (actualTorusCorrectionVelocity w x)) (ball 0 (3 * a)) := by
  have hcp : DifferentiableOn ℂ (cpartial actualComplexHarmonicRemainder) (ball 0 (8 * a)) := by
    intro z hz
    exact (HarmonicAt.differentiableAt_complex_partial
      (harmonicOnNhd_actualComplexHarmonicRemainder z (by
        rw [mem_ball_zero_iff] at hz ⊢; linarith))).differentiableWithinAt
  have hd := (cconv_differentiableOn ha hw hsupp hcp).const_mul (-I)
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply hd.congr
  intro x hx
  rw [actualTorusCorrectionVelocity_eq_harmonic ha ha16 hw hsupp hmass hsym (mem_ball_zero_iff.mp hx)]
  simp only [map_mul, conj_I, conj_conj]

end Euler2D

end
