module

public import RequestProject.Euler.ContourLogDerivative
public import RequestProject.Euler.ContourLogKernel
public import RequestProject.Euler.ContourLogFTC

/-! Actual derivatives before removing the logarithmic cutoff. The
parameter derivative identity is the integration-by-parts cancellation
that removes the second derivative of a smooth contour. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

def contourSelfThetaDeriv (z dz ddz : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  Real.log ‖z θ - z (θ + τ)‖ • ddz (θ + τ) +
    ((dz θ - dz (θ + τ)) / (z θ - z (θ + τ))).re • dz (θ + τ)

def contourSelfTauDeriv (z dz ddz : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  Real.log ‖z θ - z (θ + τ)‖ • ddz (θ + τ) +
    (-dz (θ + τ) / (z θ - z (θ + τ))).re • dz (θ + τ)

theorem hasDerivAt_contourSelfIntegrand_theta {z dz ddz : ℝ → ℂ} {θ τ : ℝ}
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hne : z θ - z (θ + τ) ≠ 0) :
    HasDerivAt (fun t => contourSelfIntegrand z dz t τ)
      (contourSelfThetaDeriv z dz ddz θ τ) θ := by
  have ht : HasDerivAt (fun t : ℝ => t + τ) 1 θ := by
    simpa only [Pi.add_apply, id_eq, add_zero] using (hasDerivAt_id θ).add_const τ
  have hzs : HasDerivAt (fun t => z (t + τ)) (dz (θ + τ)) θ := by
    simpa only [Function.comp_def, one_smul] using (hz (θ + τ)).scomp θ ht
  have hds : HasDerivAt (fun t => dz (t + τ)) (ddz (θ + τ)) θ := by
    simpa only [Function.comp_def, one_smul] using (hdz (θ + τ)).scomp θ ht
  have hl := hasDerivAt_log_norm_complex ((hz θ).sub hzs) hne
  simpa only [Pi.sub_apply, Pi.smul_apply, contourSelfIntegrand, contourLogIntegrand,
    contourSelfThetaDeriv] using hl.smul hds

theorem hasDerivAt_contourSelfIntegrand_tau {z dz ddz : ℝ → ℂ} {θ τ : ℝ}
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hne : z θ - z (θ + τ) ≠ 0) :
    HasDerivAt (contourSelfIntegrand z dz θ)
      (contourSelfTauDeriv z dz ddz θ τ) τ := by
  have ht : HasDerivAt (fun t : ℝ => θ + t) 1 τ := by
    simpa only [Pi.add_apply, id_eq, zero_add] using (hasDerivAt_const τ θ).add (hasDerivAt_id τ)
  have hzs : HasDerivAt (fun t => z (θ + t)) (dz (θ + τ)) τ := by
    simpa only [Function.comp_def, one_smul] using (hz (θ + τ)).scomp τ ht
  have hds : HasDerivAt (fun t => dz (θ + t)) (ddz (θ + τ)) τ := by
    simpa only [Function.comp_def, one_smul] using (hdz (θ + τ)).scomp τ ht
  have hh : HasDerivAt (fun t => z θ - z (θ + t)) (-dz (θ + τ)) τ := by
    simpa only [zero_sub] using (hasDerivAt_const τ (z θ)).sub hzs
  have hl := hasDerivAt_log_norm_complex hh hne
  simpa only [Pi.smul_apply, contourSelfIntegrand, contourLogIntegrand,
    contourSelfTauDeriv] using hl.smul hds

theorem contourSelfThetaDeriv_sub_tauDeriv (z dz ddz : ℝ → ℂ) (θ τ : ℝ) :
    contourSelfThetaDeriv z dz ddz θ τ - contourSelfTauDeriv z dz ddz θ τ =
      (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ) := by
  unfold contourSelfThetaDeriv contourSelfTauDeriv
  simp only [sub_div, Complex.sub_re, neg_div, Complex.neg_re, sub_smul, neg_smul]
  abel

end Euler2D

end
