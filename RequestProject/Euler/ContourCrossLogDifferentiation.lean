module

public import RequestProject.Euler.ContourCompactDifferentiation
public import RequestProject.Euler.ContourCompactSmoothIntegral
public import RequestProject.Euler.ContourLogDerivative

/-! # Actual differentiation of the separated cross-contour logarithm -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped ContDiff

namespace Euler2D

def contourCrossLogIntegrand (z w dw : ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  Real.log ‖z θ - w φ‖ • dw φ

def contourCrossLogThetaIntegrand (z dz w dw : ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  (dz θ / (z θ - w φ)).re • dw φ

def contourCrossLogIntegral (z w dw : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ φ in Icc (-Real.pi) Real.pi, contourCrossLogIntegrand z w dw θ φ

def contourCrossLogDerivativeIntegral (z dz w dw : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ φ in Icc (-Real.pi) Real.pi, contourCrossLogThetaIntegrand z dz w dw θ φ

theorem contourCrossLogIntegral_eq_intervalIntegral (z w dw : ℝ → ℂ) (θ : ℝ) :
    contourCrossLogIntegral z w dw θ =
      ∫ φ in (-Real.pi)..Real.pi, contourCrossLogIntegrand z w dw θ φ := by
  rw [contourCrossLogIntegral, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Icc_eq_integral_Ioc]

theorem hasDerivAt_contourCrossLogIntegrand {z dz w dw : ℝ → ℂ} {θ φ : ℝ}
    (hz : HasDerivAt z (dz θ) θ) (hne : z θ - w φ ≠ 0) :
    HasDerivAt (fun t => contourCrossLogIntegrand z w dw t φ)
      (contourCrossLogThetaIntegrand z dz w dw θ φ) θ := by
  have hh : HasDerivAt (fun t => z t - w φ) (dz θ) θ := by
    simpa only [sub_zero] using hz.sub_const (w φ)
  exact (hasDerivAt_log_norm_complex hh hne).smul_const (dw φ)

theorem continuousOn_contourCrossLogIntegrand {z w dw : ℝ → ℂ} {σ : ℝ}
    (hz : Continuous z) (hw : Continuous w) (hdw : Continuous dw) (hσ : 0 < σ)
    (hsep : ∀ θ φ : ℝ, φ ∈ Icc (-Real.pi) Real.pi → σ ≤ ‖z θ - w φ‖) :
    ContinuousOn (Function.uncurry (contourCrossLogIntegrand z w dw))
      (univ ×ˢ Icc (-Real.pi) Real.pi) := by
  have hch : Continuous (fun p : ℝ × ℝ => z p.1 - w p.2) :=
    (hz.comp continuous_fst).sub (hw.comp continuous_snd)
  have hn : ∀ p ∈ univ ×ˢ Icc (-Real.pi) Real.pi, ‖z p.1 - w p.2‖ ≠ 0 :=
    fun p hp => (hσ.trans_le (hsep p.1 p.2 hp.2)).ne'
  exact (hch.norm.continuousOn.log hn).smul (hdw.comp continuous_snd).continuousOn

theorem continuousOn_contourCrossLogThetaIntegrand {z dz w dw : ℝ → ℂ} {σ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hw : Continuous w) (hdw : Continuous dw)
    (hσ : 0 < σ)
    (hsep : ∀ θ φ : ℝ, φ ∈ Icc (-Real.pi) Real.pi → σ ≤ ‖z θ - w φ‖) :
    ContinuousOn (Function.uncurry (contourCrossLogThetaIntegrand z dz w dw))
      (univ ×ˢ Icc (-Real.pi) Real.pi) := by
  have hn : ∀ p ∈ univ ×ˢ Icc (-Real.pi) Real.pi, z p.1 - w p.2 ≠ 0 :=
    fun p hp => norm_pos_iff.mp (hσ.trans_le (hsep p.1 p.2 hp.2))
  have hq : ContinuousOn (fun p : ℝ × ℝ => dz p.1 / (z p.1 - w p.2))
      (univ ×ˢ Icc (-Real.pi) Real.pi) :=
    (hdz.comp continuous_fst).continuousOn.div
      ((hz.comp continuous_fst).sub (hw.comp continuous_snd)).continuousOn hn
  exact (Complex.continuous_re.comp_continuousOn hq).smul (hdw.comp continuous_snd).continuousOn

/-- Genuine differentiation under the literal compact cross-contour
integral.  Source-curve differentiation is not assumed for this step. -/
theorem hasDerivAt_contourCrossLogIntegral {z dz w dw : ℝ → ℂ} {σ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hw : Continuous w) (hdw : Continuous dw)
    (hσ : 0 < σ) (hderiv : ∀ θ, HasDerivAt z (dz θ) θ)
    (hsep : ∀ θ φ : ℝ, φ ∈ Icc (-Real.pi) Real.pi → σ ≤ ‖z θ - w φ‖) (θ : ℝ) :
    HasDerivAt (contourCrossLogIntegral z w dw)
      (contourCrossLogDerivativeIntegral z dz w dw θ) θ :=
  hasDerivAt_setIntegral_of_continuousOn_compact isCompact_Icc
    (contourCrossLogIntegrand z w dw) (contourCrossLogThetaIntegrand z dz w dw)
    (continuousOn_contourCrossLogIntegrand hz hw hdw hσ hsep)
    (continuousOn_contourCrossLogThetaIntegrand hz hdz hw hdw hσ hsep)
    (fun s φ hφ => hasDerivAt_contourCrossLogIntegrand (hderiv s)
      (norm_pos_iff.mp (hσ.trans_le (hsep s φ hφ)))) θ

theorem periodic_contourCrossLogIntegral {z w dw : ℝ → ℂ} {p : ℝ}
    (hz : Function.Periodic z p) : Function.Periodic (contourCrossLogIntegral z w dw) p := by
  intro θ
  unfold contourCrossLogIntegral
  apply integral_congr_ae
  filter_upwards [] with φ
  simp only [contourCrossLogIntegrand, hz θ]

theorem periodic_contourCrossLogDerivativeIntegral {z dz w dw : ℝ → ℂ} {p : ℝ}
    (hz : Function.Periodic z p) (hdz : Function.Periodic dz p) :
    Function.Periodic (contourCrossLogDerivativeIntegral z dz w dw) p := by
  intro θ
  unfold contourCrossLogDerivativeIntegral
  apply integral_congr_ae
  filter_upwards [] with φ
  simp only [contourCrossLogThetaIntegrand, hz θ, hdz θ]

/-- The actual nonsingular cross-interaction is smooth for true smooth
curves, by compact smooth parameter integration. -/
theorem contDiff_contourCrossLogIntegral {z w dw : ℝ → ℂ} {σ : ℝ}
    (hz : ContDiff ℝ ∞ z) (hw : ContDiff ℝ ∞ w) (hdw : ContDiff ℝ ∞ dw)
    (hσ : 0 < σ)
    (hsep : ∀ θ φ : ℝ, φ ∈ Icc (-Real.pi) Real.pi → σ ≤ ‖z θ - w φ‖) :
    ContDiff ℝ ∞ (contourCrossLogIntegral z w dw) := by
  apply contDiff_setIntegral_of_compact isCompact_Icc (contourCrossLogIntegrand z w dw)
  intro q hq
  have hch : ContDiff ℝ ∞ (fun p : ℝ × ℝ => z p.1 - w p.2) :=
    (hz.comp contDiff_fst).sub (hw.comp contDiff_snd)
  have hn : z q.1 - w q.2 ≠ 0 := norm_pos_iff.mp (hσ.trans_le (hsep q.1 q.2 hq))
  exact ((hch.contDiffAt.norm ℂ hn).log (norm_ne_zero_iff.mpr hn)).smul
    (hdw.comp contDiff_snd).contDiffAt

end Euler2D

end
