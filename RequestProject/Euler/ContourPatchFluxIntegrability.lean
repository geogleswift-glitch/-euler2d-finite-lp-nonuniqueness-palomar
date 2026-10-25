module

public import RequestProject.Euler.LogLipschitz

/-! Actual measurability and integrability of patch fluxes used in finite
interface sums; these are independent of a default integral convention. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem measurable_velocityC_of_measurable {ω : ℂ → ℝ} (hω : Measurable ω) :
    Measurable (velocityC ω) := by
  have hj : Measurable (fun p : ℂ × ℂ => (ω p.2 : ℂ) *
      (I * (p.1 - p.2) / (2 * Real.pi * ‖p.1 - p.2‖ ^ 2))) := by fun_prop
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

theorem intervalIntegrable_patchNormalFlux
    {Ω : Set ℂ} {R D : ℝ} {z dz : ℝ → ℂ}
    (hm : MeasurableSet Ω) (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    (hzc : Continuous z) (hdzc : Continuous dz) (hD : ∀ θ, ‖dz θ‖ ≤ D) :
    IntervalIntegrable (fun θ =>
      (conj (velocityC (Ω.indicator (fun _ => (1 : ℝ))) (z θ)) * dz θ).im)
      volume (0 : ℝ) (2 * Real.pi) := by
  let ω : ℂ → ℝ := Ω.indicator (fun _ => 1)
  have hωi : Integrable ω :=
    (integrableOn_const (measure_ne_top_of_subset hΩ
      (isCompact_closedBall (0 : ℂ) R).measure_ne_top)).integrable_indicator hm
  have hωm : Measurable ω := measurable_const.indicator hm
  have hωb (y : ℂ) : |ω y| ≤ 1 := by
    by_cases hy : y ∈ Ω <;> simp [ω, hy]
  let C : ℝ := 1 + (∫ y, |ω y|) / (2 * Real.pi)
  have hC : 0 ≤ C := by
    have hi : 0 ≤ ∫ y, |ω y| := integral_nonneg (fun y => abs_nonneg _)
    dsimp only [C]
    positivity
  have hV (x : ℂ) : ‖velocityC ω x‖ ≤ C := by
    simpa only [mul_one, div_one] using velocity_bound_split hωi hωb x (d := 1) (by norm_num)
  have hvm := measurable_velocityC_of_measurable hωm
  have hzmeas := hzc.measurable
  have hdzmeas := hdzc.measurable
  have hfm : Measurable (fun θ => (conj (velocityC ω (z θ)) * dz θ).im) := by fun_prop
  have hb (θ : ℝ) : ‖(conj (velocityC ω (z θ)) * dz θ).im‖ ≤ C * D := by
    rw [Real.norm_eq_abs]
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, norm_conj]
    exact mul_le_mul (hV (z θ)) (hD θ) (norm_nonneg _) hC
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hB : IntegrableOn (fun _ : ℝ => C * D) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (hB.mono' hfm.aestronglyMeasurable (ae_of_all _ hb))

end Euler2D
