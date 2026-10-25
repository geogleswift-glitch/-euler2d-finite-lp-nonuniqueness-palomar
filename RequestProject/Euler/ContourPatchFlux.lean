module

public import RequestProject.Euler.ContourRegularizedPatchFlux
public import RequestProject.Euler.ContourPatchBoundaryVelocity

/-! Actual planar patch velocity has zero normal flux through every
closed C¹ loop. Smooth regularized stream gradients have zero flux by
FTC and Fubini, and a common actual inverse-distance bound gives DCT. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem integral_normalFlux_patch_zero
    {Ω : Set ℂ} {R M D : ℝ} {z dz : ℝ → ℂ}
    (hm : MeasurableSet Ω) (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdzc : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi))
    (hM : ∀ θ, ‖z θ‖ ≤ M) (hD : ∀ θ, ‖dz θ‖ ≤ D) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (velocityC (Ω.indicator (fun _ => (1 : ℝ))) (z θ)) * dz θ).im) = 0 := by
  let F : ℝ → ℝ → ℝ := fun δ θ =>
    (conj (-I * ∫ y in Ω, regularizedLogGradient (z θ) δ y) * dz θ).im
  let U : ℝ → ℝ := fun θ =>
    (conj (velocityC (Ω.indicator (fun _ => (1 : ℝ))) (z θ)) * dz θ).im
  let K : ℝ := 2 * Real.pi * (R + M + 1)
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  have hM0 : 0 ≤ M := (norm_nonneg (z 0)).trans (hM 0)
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hdc : Measurable dz := hdzc.measurable
  have hmeas (δ : ℝ) : AEStronglyMeasurable (F δ)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    have hj : Measurable (fun p : ℝ × ℂ => regularizedLogGradient (z p.1) δ p.2) := by
      unfold regularizedLogGradient
      fun_prop
    have hi : StronglyMeasurable (fun θ => ∫ y in Ω, regularizedLogGradient (z θ) δ y) :=
      hj.stronglyMeasurable.integral_prod_right'
    have hic := hi.measurable
    have hf : Measurable (F δ) := by dsimp only [F]; fun_prop
    exact hf.aestronglyMeasurable
  have hbound (δ θ : ℝ) : ‖F δ θ‖ ≤ K * D := by
    rw [Real.norm_eq_abs]
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, norm_conj, norm_mul, norm_neg, norm_I, one_mul]
    exact mul_le_mul (norm_integral_regularizedLogGradient_le hm hR hM0 hΩ (hM θ) δ)
      (hD θ) (norm_nonneg _) hK0
  have hlim : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      Tendsto (fun δ : ℝ => F δ θ) (𝓝[>] 0) (𝓝 ((2 * Real.pi) * U θ)) := by
    apply ae_of_all
    intro θ
    have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hi := tendsto_integral_regularizedLogGradient hδ (z θ)
      (integrableOn_inverse_distance_complex_of_subset_closedBall (z θ) hR hΩ)
    have hc : Continuous (fun a : ℂ => (conj (-I * a) * dz θ).im) := by fun_prop
    have hh := hc.continuousAt.tendsto.comp hi
    have he : -I * (∫ y in Ω, (‖y - z θ‖ ^ 2)⁻¹ • (y - z θ)) =
        ((2 * Real.pi : ℝ) : ℂ) * velocityC (Ω.indicator (fun _ => (1 : ℝ))) (z θ) := by
      rw [velocityC_indicator_eq_logGradient hm]
      field_simp [Real.pi_ne_zero]
      push_cast <;> ring
    have hs (a : ℂ) :
        (conj (((2 * Real.pi : ℝ) : ℂ) * a) * dz θ).im =
          (2 * Real.pi) * (conj a * dz θ).im := by
      simp [map_mul, Complex.conj_ofReal, mul_assoc, Complex.mul_im]
    simpa only [Function.comp_def, he, hs, F, U] using hh
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hB : IntegrableOn (fun _ : ℝ => K * D) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) (fun _ => K * D)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun δ => ae_of_all _ (hbound δ)) hB hlim
  have hzero : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F δ θ) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have he := integral_normalFlux_regularizedPatch_zero hδ.ne' hΩ hz hdzc hp
    simpa only [intervalIntegral.integral_of_le hab, F] using he
  have heq : (fun δ : ℝ => ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F δ θ) =ᶠ[𝓝[>] 0]
      (fun _ => 0) := hzero
  have hzlim : Tendsto (fun δ : ℝ => ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F δ θ)
      (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' heq.symm
  have he := tendsto_nhds_unique hDCT hzlim
  rw [integral_const_mul] at he
  have hUi : (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), U θ) = 0 :=
    (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  simpa only [intervalIntegral.integral_of_le hab, U] using hUi

end Euler2D
