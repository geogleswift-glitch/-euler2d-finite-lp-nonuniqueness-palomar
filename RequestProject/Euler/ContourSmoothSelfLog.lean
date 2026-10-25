module

public import RequestProject.Euler.ContourSmoothDividedChord
public import RequestProject.Euler.ContourWeightedCompactSmoothIntegral
public import RequestProject.Euler.ContourLogKernel

/-!
# Actual smoothness of the logarithmic self-contour operator

The genuine logarithmic kernel is almost everywhere the sum of the fixed
integrable weight `log τ` and the smooth logarithm of the normalized chord.
This proves smoothness of the actual integral, including every derivative,
without supposing any smoothness of the resulting operator.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff

namespace Euler2D

theorem contourLogIntegrand_eq_log_add_normalized {z : ℝ → ℂ}
    (hz : ContDiff ℝ 1 z) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) (hne : τ ≠ 0) :
    contourLogIntegrand z θ τ = Real.log τ + Real.log ‖smoothContourNormalizedChord z θ τ‖ := by
  have hn := smoothContourNormalizedChord_ne_zero hz hc hchord θ τ hτ
  have he : ‖z θ - z (θ + τ)‖ = |τ| * ‖smoothContourNormalizedChord z θ τ‖ := by
    rw [norm_sub_rev, ← smul_smoothContourNormalizedChord hz θ τ, norm_smul, Real.norm_eq_abs]
  rw [contourLogIntegrand, he, Real.log_mul (abs_ne_zero.mpr hne) (norm_ne_zero_iff.mpr hn),
    Real.log_abs]

private lemma smoothSelfLog_joint_normalized {z : ℝ → ℂ}
    (hz : ContDiff ℝ ∞ z) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-Real.pi) Real.pi) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      Real.log ‖smoothContourNormalizedChord z p.1 p.2‖ • deriv z (p.1 + p.2)) q := by
  have hdz : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  exact (contDiffAt_log_norm_smoothContourNormalizedChord hz hc hchord q (abs_le.mpr hq)).smul
    (hdz.comp (contDiff_fst.add contDiff_snd)).contDiffAt

set_option maxHeartbeats 600000 in
/-- Actual smoothness of the genuine logarithmic self-contour integral.
The sole geometric assumption is the genuine positive short-chord bound. -/
theorem contDiff_contourSelfIntegral_of_smooth_chord {z : ℝ → ℂ}
    (hz : ContDiff ℝ ∞ z) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ContDiff ℝ ∞ (contourSelfIntegral z (deriv z)) := by
  let S : Set ℝ := Icc (-Real.pi) Real.pi
  have hS : IsCompact S := isCompact_Icc
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      intervalIntegral.intervalIntegrable_log'
  have hdz : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  have hdshift : ContDiff ℝ ∞ (fun q : ℝ × ℝ => deriv z (q.1 + q.2)) :=
    hdz.comp (contDiff_fst.add contDiff_snd)
  have hscale : ContDiff ℝ ∞ (fun θ : ℝ =>
      ∫ τ in S, Real.log τ • deriv z (θ + τ)) :=
    contDiff_weightedSetIntegral_of_compact hS hw
      (fun θ τ : ℝ => deriv z (θ + τ)) (fun _ _ => hdshift.contDiffAt)
  have hn (q : ℝ × ℝ) (hq : q.2 ∈ S) : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      Real.log ‖smoothContourNormalizedChord z p.1 p.2‖ • deriv z (p.1 + p.2)) q :=
    smoothSelfLog_joint_normalized hz hc hchord q hq
  have hnormal : ContDiff ℝ ∞ (fun θ : ℝ =>
      ∫ τ in S, Real.log ‖smoothContourNormalizedChord z θ τ‖ • deriv z (θ + τ)) :=
    contDiff_setIntegral_of_compact hS
      (fun θ τ : ℝ => Real.log ‖smoothContourNormalizedChord z θ τ‖ • deriv z (θ + τ)) hn
  have heq (θ : ℝ) : contourSelfIntegral z (deriv z) θ =
      (∫ τ in S, Real.log τ • deriv z (θ + τ)) +
        (∫ τ in S, Real.log ‖smoothContourNormalizedChord z θ τ‖ • deriv z (θ + τ)) := by
    have hdcont : ContinuousOn (fun τ : ℝ => deriv z (θ + τ)) S :=
      (hdz.continuous.comp (continuous_const.add continuous_id)).continuousOn
    have hni : IntegrableOn (fun τ : ℝ =>
        Real.log ‖smoothContourNormalizedChord z θ τ‖ • deriv z (θ + τ)) S := by
      apply ContinuousOn.integrableOn_compact hS
      have hj : ContinuousOn (fun p : ℝ × ℝ =>
          Real.log ‖smoothContourNormalizedChord z p.1 p.2‖ • deriv z (p.1 + p.2)) (univ ×ˢ S) :=
        fun q hq => (hn q hq.2).continuousAt.continuousWithinAt
      have hpair : ContinuousOn (fun τ : ℝ => (θ, τ)) S :=
        (continuous_const.prodMk continuous_id).continuousOn
      exact (hj.comp hpair (fun _ hτ => ⟨mem_univ _, hτ⟩)).congr (fun _ _ => rfl)
    have hwi := integrableOn_smul_continuousOn_compact hS hw hdcont
    rw [contourSelfIntegral, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc, ← integral_add hwi hni]
    apply integral_congr_ae
    have hn0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, setOf_eq_eq_singleton, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn0] with τ hτ hne
    change contourLogIntegrand z θ τ • deriv z (θ + τ) = _
    rw [contourLogIntegrand_eq_log_add_normalized (hz.of_le (by simp)) hc hchord
      θ τ (abs_le.mpr hτ) hne, add_smul]
  have hfun : contourSelfIntegral z (deriv z) = (fun θ =>
      (∫ τ in S, Real.log τ • deriv z (θ + τ)) +
        (∫ τ in S, Real.log ‖smoothContourNormalizedChord z θ τ‖ • deriv z (θ + τ))) := funext heq
  rw [hfun]
  exact hscale.add hnormal

end Euler2D

end
