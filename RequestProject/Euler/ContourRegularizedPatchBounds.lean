module

public import RequestProject.Euler.ContourLogGradientIntegrability
public import RequestProject.Euler.LogLipschitz

/-! Actual bounded-domain regularized gradient integrals, with a common
bound independent of the regularization parameter. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem regularizedLogGradient_swap (x y : ℂ) (δ : ℝ) :
    regularizedLogGradient y δ x = -regularizedLogGradient x δ y := by
  unfold regularizedLogGradient
  rw [norm_sub_rev, ← smul_neg]
  congr 1
  abel

theorem integrableOn_regularizedLogGradient_of_subset_closedBall
    {Ω : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    (x : ℂ) (δ : ℝ) : IntegrableOn (regularizedLogGradient x δ) Ω :=
  (integrableOn_inverse_distance_complex_of_subset_closedBall x hR hΩ).mono'
    (measurable_regularizedLogGradient x δ).aestronglyMeasurable
    (ae_of_all _ (norm_regularizedLogGradient_le x δ))

theorem norm_integral_regularizedLogGradient_le
    {Ω : Set ℂ} {R M : ℝ} (hm : MeasurableSet Ω)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    {x : ℂ} (hx : ‖x‖ ≤ M) (δ : ℝ) :
    ‖∫ y in Ω, regularizedLogGradient x δ y‖ ≤ 2 * Real.pi * (R + M + 1) := by
  let L := R + M + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hB : Integrable (fun y : ℂ => truncInvNorm L (y - x)) :=
    (integrable_truncInvNorm L).comp_sub_right x
  have hb : ∀ y : ℂ,
      ‖Ω.indicator (regularizedLogGradient x δ) y‖ ≤ truncInvNorm L (y - x) := by
    intro y
    by_cases hy : y ∈ Ω
    · rw [indicator_of_mem hy]
      have hyl : ‖y - x‖ < L := by
        have hyR := mem_closedBall_zero_iff.mp (hΩ hy)
        have ht := norm_sub_le y x
        dsimp only [L]
        linarith
      rw [truncInvNorm, if_pos hyl]
      exact norm_regularizedLogGradient_le x δ y
    · rw [indicator_of_notMem hy, norm_zero]
      exact truncInvNorm_nonneg L (y - x)
  calc
    _ = ‖∫ y, Ω.indicator (regularizedLogGradient x δ) y‖ := by rw [integral_indicator hm]
    _ ≤ ∫ y, truncInvNorm L (y - x) := norm_integral_le_of_norm_le hB (ae_of_all _ hb)
    _ = _ := by rw [integral_sub_right_eq_self, integral_truncInvNorm hL]

theorem continuous_regularizedLogPotentialDerivative_pair {δ : ℝ} (hδ : δ ≠ 0) :
    Continuous (fun p : ℂ × ℂ => regularizedLogPotentialDerivative p.1 δ p.2) := by
  have hc : Continuous (fun p : ℂ × ℂ => δ ^ 2 + ‖p.2 - p.1‖ ^ 2) := by fun_prop
  exact (hc.inv₀ (fun p => (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hδ)
    (sq_nonneg ‖p.2 - p.1‖)).ne')).smul
      ((innerSL ℝ).continuous.comp (continuous_snd.sub continuous_fst))

end Euler2D
