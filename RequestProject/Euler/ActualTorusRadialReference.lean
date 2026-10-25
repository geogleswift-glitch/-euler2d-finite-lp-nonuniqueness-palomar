module

public import RequestProject.Euler.ActualTorusCorrectionAnalytic
public import RequestProject.Euler.PeriodicCorrection
public import RequestProject.Euler.ContourAnnularPerturbation
public import RequestProject.Euler.CircularFiniteContourDensity

/-! The actual periodic correction of a radial zero-mass reference
vanishes exactly. The harmonic mean value identity is applied to both
components of the actual holomorphic partial of the constructed Green
remainder. Thus no absolute periodic-error baseline is introduced when
the true source is compared with its circular reference. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem cconv_analytic_radial_zero {a : ℝ} (ha : 0 < a)
    {w : ℂ → ℝ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 (8 * a))) (hw : Integrable w)
    (hsupp : ∀ y, a < ‖y‖ → w y = 0)
    (hrad : ∀ (θ : ℝ) (y : ℂ), w (exp ((θ : ℂ) * I) * y) = w y)
    (hmass : ∫ y, w y = 0) {x : ℂ} (hx : ‖x‖ ≤ a) :
    cconv w g x = 0 := by
  have hcont : ContinuousOn g (closedBall 0 (3 * a)) :=
    hg.continuousOn.mono (closedBall_subset_ball (by linarith))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (3 * a)).exists_bound_of_continuousOn hcont
  have hint : Integrable (fun y => (w y : ℂ) * g (x - y)) :=
    integrable_cconv hw hsupp hcont hB (by linarith)
  have hre := radial_harmonic_conv_zero ha
    (fun z hz => (hg z hz).harmonicAt_re) hw hsupp hrad hmass hx
  have him := radial_harmonic_conv_zero ha
    (fun z hz => (hg z hz).harmonicAt_im) hw hsupp hrad hmass hx
  have hRe := integral_re hint
  have hIm := integral_im hint
  simp only [RCLike.re_to_complex] at hRe
  simp only [RCLike.im_to_complex] at hIm
  apply Complex.ext
  · change (∫ y, (w y : ℂ) * g (x - y)).re = 0
    rw [← hRe]
    simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero, mul_comm] using hre
  · change (∫ y, (w y : ℂ) * g (x - y)).im = 0
    rw [← hIm]
    simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, mul_zero, zero_add, add_zero, mul_comm] using him

theorem actualTorusCorrectionVelocity_radial_zero {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) {w : ℂ → ℝ}
    (hw : Integrable w) (hsupp : ∀ y, a < ‖y‖ → w y = 0)
    (hrad : ∀ (θ : ℝ) (y : ℂ), w (exp ((θ : ℂ) * I) * y) = w y)
    (hmass : ∫ y, w y = 0) {x : ℂ} (hx : ‖x‖ ≤ a) :
    actualTorusCorrectionVelocity w x = 0 := by
  have hsym : ∀ y, w (I * y) = w y := by
    intro y
    have hh := hrad (Real.pi / 2) y
    rw [show (((Real.pi / 2 : ℝ) : ℂ) * I) = (Real.pi / 2 : ℂ) * I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I] at hh
    exact hh
  have hg : AnalyticOnNhd ℂ (cpartial actualComplexHarmonicRemainder) (ball 0 (8 * a)) := by
    intro z hz
    apply HarmonicAt.analyticAt_complex_partial
    apply harmonicOnNhd_actualComplexHarmonicRemainder
    rw [mem_ball_zero_iff] at hz ⊢
    linarith only [hz, ha16]
  rw [actualTorusCorrectionVelocity_eq_harmonic ha ha16 hw hsupp hmass hsym
    (by linarith only [hx, ha]), cconv_analytic_radial_zero ha hg hw hsupp hrad hmass hx]
  simp

theorem actualTorusCorrectionVelocity_finite_circles_zero
    {ι : Type*} [Fintype ι] {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (g r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i ≤ a)
    (hmass : ∑ i, g i * r i ^ 2 = 0) {x : ℂ} (hx : ‖x‖ ≤ a) :
    actualTorusCorrectionVelocity (fun y => ∑ i, g i * circlePatchVorticity (r i) y) x = 0 := by
  classical
  have hw : Integrable (fun y => ∑ i, g i * circlePatchVorticity (r i) y) :=
    integrable_finset_sum _ (fun i _ => (integrable_circlePatchVorticity (r i)).const_mul (g i))
  have hsupp : ∀ y : ℂ, a < ‖y‖ → (∑ i, g i * circlePatchVorticity (r i) y) = 0 := by
    intro y hy
    apply Finset.sum_eq_zero
    intro i _
    have hnot : y ∉ ball (0 : ℂ) (r i) := by
      rw [mem_ball_zero_iff, not_lt]
      exact (hra i).trans hy.le
    rw [circlePatchVorticity, indicator_of_notMem hnot, mul_zero]
  have hrad : ∀ (θ : ℝ) (y : ℂ),
      (∑ i, g i * circlePatchVorticity (r i) (exp ((θ : ℂ) * I) * y)) =
        ∑ i, g i * circlePatchVorticity (r i) y := by
    intro θ y
    apply Finset.sum_congr rfl
    intro i _
    have he : ‖exp ((θ : ℂ) * I) * y‖ = ‖y‖ := by
      rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
    by_cases hy : ‖y‖ < r i <;> simp [circlePatchVorticity, mem_ball_zero_iff, he, hy]
  have hmassI : (∫ y : ℂ, ∑ i, g i * circlePatchVorticity (r i) y) = 0 := by
    calc
      _ = Real.pi * ∑ i, g i * r i ^ 2 := by
        rw [integral_finset_sum Finset.univ (fun i _ => (integrable_circlePatchVorticity (r i)).const_mul (g i)),
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul, integral_circlePatchVorticity (hr i)]
        ring
      _ = 0 := by rw [hmass, mul_zero]
  exact actualTorusCorrectionVelocity_radial_zero ha ha16 hw hsupp hrad hmassI hx

theorem actualTorusCorrectionVelocity_circular_cell_zero
    {A₀ b R ρ a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hR : 0 < R) (hρ : 0 < ρ) {N : ℕ} (j : Fin (N + 1))
    (hrja : radScale R ρ j ≤ a) {x : ℂ} (hx : ‖x‖ ≤ a) :
    actualTorusCorrectionVelocity
      (fun y => ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
        circlePatchVorticity (circularContourRadii i * radScale R ρ j) y) x = 0 := by
  apply actualTorusCorrectionVelocity_finite_circles_zero ha ha16
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => circularContourRadii i * radScale R ρ j)
  · exact fun i => mul_nonneg (circularContourRadii_bounds i).1.le (radScale_pos hR hρ j).le
  · intro i
    exact (mul_le_of_le_one_left (radScale_pos hR hρ j).le
      (circularContourRadii_bounds i).2.2).trans hrja
  · simp only [finiteCircularInterfaceStrength, Fin.sum_univ_two,
      circularContourStrengths, circularContourRadii, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_pow]
    rw [cellA_sq]
    ring
  · exact hx

end Euler2D

end
