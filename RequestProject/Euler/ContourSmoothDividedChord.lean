module

public import RequestProject.Euler.ContourCompactSmoothIntegral
public import RequestProject.Euler.ContourDerivativeLower
public import RequestProject.Euler.ContourSmoothEmbedding
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The genuine smooth extension of a normalized contour chord

The extension is the actual integral of the actual derivative along the
unit segment.  The fundamental theorem of calculus identifies it with
the divided chord away from zero and with the derivative at zero.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff

namespace Euler2D

def smoothContourNormalizedChord (z : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv z (θ + u * τ)

@[simp] theorem smoothContourNormalizedChord_zero (z : ℝ → ℂ) (θ : ℝ) :
    smoothContourNormalizedChord z θ 0 = deriv z θ := by
  simp [smoothContourNormalizedChord, intervalIntegral.integral_const]

/-- The actual FTC identity, including the degenerate chord at zero. -/
theorem smul_smoothContourNormalizedChord {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) (θ τ : ℝ) :
    τ • smoothContourNormalizedChord z θ τ = z (θ + τ) - z θ := by
  have hc : ContinuousOn (fun u : ℝ => deriv z (θ + u • τ)) (Icc 0 1) :=
    (hz.continuous_deriv_one.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  simpa only [smul_eq_mul, smoothContourNormalizedChord] using
    (intervalIntegral.integral_unitInterval_deriv_eq_sub
      (𝕜 := ℝ) (f := z) (f' := deriv z) (z₀ := θ) (z₁ := τ) hc
      (fun u _ => (hz.differentiable_one (θ + u • τ)).hasDerivAt))

theorem smoothContourNormalizedChord_eq_div {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z)
    (θ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    smoothContourNormalizedChord z θ τ = (z (θ + τ) - z θ) / (τ : ℂ) := by
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hτ)).mpr
  have hh := smul_smoothContourNormalizedChord hz θ τ
  simpa only [Complex.real_smul, mul_comm] using hh

/-- Genuine joint smoothness across `τ = 0`, proved by compact integration. -/
theorem contDiff_smoothContourNormalizedChord {z : ℝ → ℂ} (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothContourNormalizedChord z p.1 p.2) := by
  have hdz : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  have hF : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      deriv z (q.1.1 + q.2 * q.1.2)) :=
    hdz.comp (contDiff_fst.fst.add (contDiff_snd.mul contDiff_fst.snd))
  have hi := contDiff_setIntegral_of_compact (P := ℝ × ℝ) (S := Icc (0 : ℝ) 1) isCompact_Icc
    (fun p : ℝ × ℝ => fun u : ℝ => deriv z (p.1 + u * p.2))
    (fun q _ => hF.contDiffAt)
  have heq : (fun p : ℝ × ℝ => smoothContourNormalizedChord z p.1 p.2) =
      (fun p : ℝ × ℝ => ∫ u in Icc (0 : ℝ) 1, deriv z (p.1 + u * p.2)) := by
    funext p
    rw [smoothContourNormalizedChord, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hi

theorem periodic_smoothContourNormalizedChord {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z)
    (hp : Function.Periodic z (2 * Real.pi)) (τ : ℝ) :
    Function.Periodic (fun θ => smoothContourNormalizedChord z θ τ) (2 * Real.pi) := by
  have hd := periodic_deriv_contour hp hz.differentiable_one
  intro θ
  unfold smoothContourNormalizedChord
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show θ + 2 * Real.pi + u * τ = (θ + u * τ) + 2 * Real.pi by ring, hd]

/-- The true short-chord lower bound persists on the entire normalized
extension, including its actual derivative value at zero. -/
theorem norm_smoothContourNormalizedChord_lower {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) {c : ℝ}
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) : c ≤ ‖smoothContourNormalizedChord z θ τ‖ := by
  by_cases hzero : τ = 0
  · subst τ
    rw [smoothContourNormalizedChord_zero]
    exact norm_hasDerivAt_lower_of_chord (hz.differentiable_one θ).hasDerivAt
      Real.pi_pos (hchord θ)
  · have hh := hchord θ τ hτ
    have he : ‖z θ - z (θ + τ)‖ = |τ| * ‖smoothContourNormalizedChord z θ τ‖ := by
      rw [norm_sub_rev, ← smul_smoothContourNormalizedChord hz θ τ, norm_smul, Real.norm_eq_abs]
    rw [he, mul_comm c] at hh
    exact le_of_mul_le_mul_left hh (abs_pos.mpr hzero)

theorem smoothContourNormalizedChord_ne_zero {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) {c : ℝ}
    (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) : smoothContourNormalizedChord z θ τ ≠ 0 :=
  norm_pos_iff.mp (hc.trans_le (norm_smoothContourNormalizedChord_lower hz hchord θ τ hτ))

/-- Smoothness of the actual normalized logarithm at every point of the
closed short-chord strip, with no removed diagonal. -/
theorem contDiffAt_log_norm_smoothContourNormalizedChord {z : ℝ → ℂ}
    (hz : ContDiff ℝ ∞ z) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (p : ℝ × ℝ) (hp : |p.2| ≤ Real.pi) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => Real.log ‖smoothContourNormalizedChord z q.1 q.2‖) p := by
  have hn := smoothContourNormalizedChord_ne_zero (hz.of_le (by simp)) hc hchord p.1 p.2 hp
  exact ((contDiff_smoothContourNormalizedChord hz).contDiffAt.norm ℂ hn).log
    (norm_ne_zero_iff.mpr hn)

def smoothContourNormalizedChordRatio (z w : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  smoothContourNormalizedChord z θ τ / smoothContourNormalizedChord w θ τ

theorem smoothContourNormalizedChordRatio_eq_div {z w : ℝ → ℂ}
    (hz : ContDiff ℝ 1 z) (hw : ContDiff ℝ 1 w) (θ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    smoothContourNormalizedChordRatio z w θ τ =
      (z (θ + τ) - z θ) / (w (θ + τ) - w θ) := by
  rw [smoothContourNormalizedChordRatio, smoothContourNormalizedChord_eq_div hz θ hτ,
    smoothContourNormalizedChord_eq_div hw θ hτ,
    div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hτ)]

/-- The genuine logarithmic chord ratio extends smoothly across the
diagonal whenever both actual curves have positive short-chord bounds. -/
theorem contDiffAt_log_norm_smoothContourNormalizedChordRatio {z w : ℝ → ℂ}
    (hz : ContDiff ℝ ∞ z) (hw : ContDiff ℝ ∞ w) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hzc : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hwd : ∀ θ τ : ℝ, |τ| ≤ Real.pi → d * |τ| ≤ ‖w θ - w (θ + τ)‖)
    (p : ℝ × ℝ) (hp : |p.2| ≤ Real.pi) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
      Real.log ‖smoothContourNormalizedChordRatio z w q.1 q.2‖) p := by
  have hnz := smoothContourNormalizedChord_ne_zero (hz.of_le (by simp)) hc hzc p.1 p.2 hp
  have hnw := smoothContourNormalizedChord_ne_zero (hw.of_le (by simp)) hd hwd p.1 p.2 hp
  have hq : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
      smoothContourNormalizedChordRatio z w q.1 q.2) p :=
    ((contDiff_smoothContourNormalizedChord hz).contDiffAt.mul
      ((contDiff_smoothContourNormalizedChord hw).contDiffAt.inv hnw)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => div_eq_mul_inv _ _))
  exact (hq.norm ℂ (div_ne_zero hnz hnw)).log (norm_ne_zero_iff.mpr (div_ne_zero hnz hnw))

end Euler2D

end
