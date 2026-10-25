module

public import RequestProject.Euler.ContourLogTruncatedDifferentiation
public import RequestProject.Euler.ContourLogBoundary
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Closing the actual log-integral derivative once its spatial Cauchy
cutoffs have a genuine uniform limit. The boundary contribution is proved
to vanish, and the functions themselves converge to the original integral. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

theorem hasDerivAt_contourSelfIntegral_of_spatialCutoff_limit
    {z dz ddz G : ℝ → ℂ} {γ H c M D : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hddzc : Continuous ddz)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hc : 0 < c)
    (hM : ∀ s, ‖z s‖ ≤ M) (hD : ∀ s, ‖dz s‖ ≤ D)
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hzper : Function.Periodic z (2 * Real.pi)) (hdzper : Function.Periodic dz (2 * Real.pi))
    (hG : TendstoUniformly
      (fun δ θ => ∫ τ in symmetricContourTruncation Real.pi δ,
        (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) G (𝓝[>] (0 : ℝ))) (θ : ℝ) :
    HasDerivAt (contourSelfIntegral z dz) (G θ) θ := by
  have hB := tendstoUniformly_contourSelfCutoffBoundary hγ hH hc hM hD hz hd hchord
  have hU : TendstoUniformly
      (fun δ θ => (∫ τ in symmetricContourTruncation Real.pi δ,
        (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) + contourSelfCutoffBoundary z dz δ θ)
      G (𝓝[>] (0 : ℝ)) := by
    simpa only [Pi.add_def, add_zero] using hG.add hB
  have hF := tendstoUniformly_contourSelfIntegralTruncated hzc hdzc hc hM hD hchord
  have hfg (x : ℝ) : Tendsto (fun δ => contourSelfIntegralTruncated z dz δ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (contourSelfIntegral z dz x)) :=
    (TendstoUniformly.tendsto_at hF x).mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds Real.pi_pos)
  have hdiff : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), ∀ x : ℝ,
      HasDerivAt (contourSelfIntegralTruncated z dz δ)
        ((∫ τ in symmetricContourTruncation Real.pi δ,
          (dz x / (z x - z (x + τ))).re • dz (x + τ)) + contourSelfCutoffBoundary z dz δ x) x := by
    filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ hδπ x
    exact hasDerivAt_contourSelfIntegralTruncated_eq hzc hdzc hddzc hc hδ hδπ.le
      hz hdz hchord hzper hdzper x
  exact hasDerivAt_of_tendstoUniformly hU hdiff hfg θ

end Euler2D

end
