module

public import RequestProject.Euler.ContourGreenFormula
public import RequestProject.Euler.ContourLogBoundaryLimit
public import RequestProject.Euler.ContourLogGradientIntegrability
public import RequestProject.Euler.Exterior

/-! The actual planar Biot–Savart velocity of the actual enclosed patch
equals the original contour boundary integral, including at the boundary.
The singular formula follows by two genuine dominated-convergence limits. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

theorem integral_regularizedLogGradient_nearCircleEnclosedDomain
    {z dz : ℝ → ℂ} {r ε δ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hdz : Continuous dz) (hp : Function.Periodic z (2 * Real.pi))
    (hδ : δ ≠ 0) (x : ℂ) :
    (∫ y in nearCircleEnclosedDomain hr hε hsmall hz hv hd, regularizedLogGradient x δ y) =
      -I * contourRegularizedLogBoundaryIntegral z dz δ x := by
  have hg := integral_gradient_nearCircleEnclosedDomain hr hε hsmall hz hv hd hdz hp
    (hasFDerivAt_regularizedLogPotential x hδ)
    (continuous_regularizedLogPotentialDerivative x hδ)
  simpa only [complexRealGradient_regularizedLogPotentialDerivative,
    regularizedLogPotential, contourRegularizedLogBoundaryIntegral, Complex.real_smul,
    norm_sub_rev] using hg

theorem integral_logGradient_nearCircleEnclosedDomain
    {z dz : ℝ → ℂ} {r ε c M D : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hdz : Continuous dz) (hp : Function.Periodic z (2 * Real.pi))
    (hdp : Function.Periodic dz (2 * Real.pi))
    (hc : 0 < c) (hM : ∀ θ, ‖z θ‖ ≤ M) (hD : ∀ θ, ‖dz θ‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (x : ℂ) :
    (∫ y in nearCircleEnclosedDomain hr hε hsmall hz hv hd,
      (‖y - x‖ ^ 2)⁻¹ • (y - x)) = -I * contourLogBoundaryIntegral z dz x := by
  let Ω := nearCircleEnclosedDomain hr hε hsmall hz hv hd
  have hdom : IntegrableOn (fun y : ℂ => ‖y - x‖⁻¹) Ω :=
    integrableOn_inverse_distance_complex_of_subset_closedBall x (add_nonneg hr.le hε)
      ((nearCircleEnclosedDomain_subset_ball hr hε hsmall hz hv hd).trans
        Metric.ball_subset_closedBall)
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hA := tendsto_integral_regularizedLogGradient hδ x hdom
  have hB : Tendsto (fun δ : ℝ => contourRegularizedLogBoundaryIntegral z dz δ x) (𝓝[>] 0)
      (𝓝 (contourLogBoundaryIntegral z dz x)) := (tendsto_contourRegularizedLogBoundaryIntegral
    (continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)) hdz hc hM hD hca hp hdp x).mono_left
      nhdsWithin_le_nhds
  have he : (fun δ : ℝ => ∫ y in Ω, regularizedLogGradient x δ y) =ᶠ[𝓝[>] 0]
      fun δ => -I * contourRegularizedLogBoundaryIntegral z dz δ x := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact integral_regularizedLogGradient_nearCircleEnclosedDomain
      hr hε hsmall hz hv hd hdz hp (ne_of_gt hδ) x
  exact tendsto_nhds_unique hA ((hB.const_mul (-I)).congr' he.symm)

theorem velocityC_indicator_eq_logGradient {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (x : ℂ) :
    velocityC (Ω.indicator (fun _ => (1 : ℝ))) x =
      (-I / (2 * Real.pi) : ℂ) * (∫ y in Ω, (‖y - x‖ ^ 2)⁻¹ • (y - x)) := by
  rw [velocityC, ← integral_const_mul, ← integral_indicator hΩ]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    by_cases hy : y ∈ Ω
    · simp only [indicator_of_mem hy, ofReal_one, one_mul, Complex.real_smul]
      rw [norm_sub_rev]
      push_cast
      rw [show y - x = -(x - y) by ring]
      ring
    · simp only [indicator_of_notMem hy, ofReal_zero, zero_mul])

/-- The literal original patch velocity is exactly the boundary field. -/
theorem velocityC_nearCircleEnclosedDomain_eq_boundaryIntegral
    {z dz : ℝ → ℂ} {r ε c M D : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)
    (hdz : Continuous dz) (hp : Function.Periodic z (2 * Real.pi))
    (hdp : Function.Periodic dz (2 * Real.pi))
    (hc : 0 < c) (hM : ∀ θ, ‖z θ‖ ≤ M) (hD : ∀ θ, ‖dz θ‖ ≤ D)
    (hca : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (x : ℂ) :
    velocityC ((nearCircleEnclosedDomain hr hε hsmall hz hv hd).indicator (fun _ => (1 : ℝ))) x =
      (-1 / (2 * Real.pi) : ℂ) * contourLogBoundaryIntegral z dz x := by
  rw [velocityC_indicator_eq_logGradient
    (isOpen_nearCircleEnclosedDomain hr hε hsmall hz hv hd hp).measurableSet,
    integral_logGradient_nearCircleEnclosedDomain hr hε hsmall hz hv hd hdz hp hdp hc hM hD hca]
  have hI : I ^ 2 = (-1 : ℂ) := I_sq
  calc
    _ = (I ^ 2 / (2 * Real.pi) : ℂ) * contourLogBoundaryIntegral z dz x := by ring
    _ = _ := by rw [hI]

end Euler2D

end
