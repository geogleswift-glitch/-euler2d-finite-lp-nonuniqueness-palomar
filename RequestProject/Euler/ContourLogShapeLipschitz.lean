module

public import RequestProject.Euler.ContourLogShapeBounds
public import RequestProject.Euler.ContourLogCircle

/-! Quantitative genuine uniform-norm shape continuity of the original
logarithmic self-interaction, from actual common chord and norm bounds. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

def contourLogShapeConstant (c M : ℝ) : ℝ :=
  (∫ τ in (-Real.pi)..Real.pi, contourLogMajorant c M τ) + 2 * Real.pi * (M / c)

theorem norm_contourSelfIntegral_sub_le {z dz w dw : ℝ → ℂ} {ε c M : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hwc : Continuous w) (hdwc : Continuous dw)
    (hc : 0 < c) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hp : ContDiff ℝ 1 (fun t => z t - w t))
    (hd : ∀ t, ‖deriv (fun s => z s - w s) t‖ ≤ ε)
    (hMz : ∀ t, ‖z t‖ ≤ M) (hMw : ∀ t, ‖w t‖ ≤ M)
    (hDz : ∀ t, ‖dz t‖ ≤ M) (hDw : ∀ t, ‖dw t‖ ≤ M)
    (hdiff : ∀ t, ‖dz t - dw t‖ ≤ ε)
    (hZ : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hW : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖w θ - w (θ + τ)‖) (θ : ℝ) :
    ‖contourSelfIntegral z dz θ - contourSelfIntegral w dw θ‖ ≤
      ε * contourLogShapeConstant c M := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hiZ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (intervalIntegrable_contourSelfIntegrand hzc hdzc hc hMz hDz hZ θ)
  have hiW := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (intervalIntegrable_contourSelfIntegrand hwc hdwc hc hMw hDw hW θ)
  have hBi : IntervalIntegrable (fun τ => ε * (contourLogMajorant c M τ + M / c))
      volume (-Real.pi) Real.pi :=
    ((intervalIntegrable_contourLogMajorant c M).add intervalIntegrable_const).const_mul ε
  unfold contourSelfIntegral
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_sub hiZ hiW]
  calc
    _ ≤ ∫ τ in Ioc (-Real.pi) Real.pi, ε * (contourLogMajorant c M τ + M / c) := by
      apply norm_integral_le_of_norm_le ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hBi)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
      exact norm_contourSelfIntegrand_sub_le hc hε hM hp hd hMz hdiff hDw hZ hW
        (abs_le.mpr ⟨hτ.1.le, hτ.2⟩)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (intervalIntegrable_contourLogMajorant c M) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      unfold contourLogShapeConstant
      ring

theorem norm_contourC1SelfIntegral_sub_le {γ : ℝ≥0} (Z W : ContourC1Space γ) {c M : ℝ}
    (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c)
    (hW : ContourC1Space.HasChordArcLower W c) (hMZ : ‖Z‖ ≤ M) (hMW : ‖W‖ ≤ M) (θ : ℝ) :
    ‖ContourC1Space.selfLogIntegral Z θ - ContourC1Space.selfLogIntegral W θ‖ ≤
      ‖Z - W‖ * contourLogShapeConstant c M := by
  have hp : ContDiff ℝ 1 (fun t => ContourC1Space.lift γ Z t - ContourC1Space.lift γ W t) := by
    simpa only [ContourC1Space.lift_sub, Pi.sub_apply] using ContourC1Space.contDiff_lift (Z - W)
  have hd : ∀ t, ‖deriv (fun s => ContourC1Space.lift γ Z s - ContourC1Space.lift γ W s) t‖ ≤ ‖Z - W‖ := by
    intro t
    simpa only [ContourC1Space.lift_sub, Pi.sub_apply] using ContourC1Space.norm_deriv_lift_le (Z - W) t
  have hdiff (t : ℝ) :
      ‖deriv (ContourC1Space.lift γ Z) t - deriv (ContourC1Space.lift γ W) t‖ ≤ ‖Z - W‖ := by
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
    change ‖ContourC1Space.derivative γ (Z - W) (t : ContourCircle)‖ ≤ ‖Z - W‖
    simpa only [ContourC1Space.deriv_lift] using ContourC1Space.norm_deriv_lift_le (Z - W) t
  exact norm_contourSelfIntegral_sub_le
    (ContourC1Space.contDiff_lift Z).continuous (ContourC1Space.contDiff_lift Z).continuous_deriv_one
    (ContourC1Space.contDiff_lift W).continuous (ContourC1Space.contDiff_lift W).continuous_deriv_one
    hc (norm_nonneg (Z - W)) ((norm_nonneg Z).trans hMZ) hp hd
    (fun t => (ContourC1Space.norm_eval_le Z (t : ContourCircle)).trans hMZ)
    (fun t => (ContourC1Space.norm_eval_le W (t : ContourCircle)).trans hMW)
    (fun t => (ContourC1Space.norm_deriv_lift_le Z t).trans hMZ)
    (fun t => (ContourC1Space.norm_deriv_lift_le W t).trans hMW) hdiff hZ hW θ

theorem norm_selfLogCircleBCF_sub_le {γ : ℝ≥0}
    (Z W : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z}) {c M : ℝ}
    (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z.val c)
    (hW : ContourC1Space.HasChordArcLower W.val c) (hMZ : ‖Z.val‖ ≤ M) (hMW : ‖W.val‖ ≤ M) :
    ‖ContourC1Space.selfLogCircleBCF Z - ContourC1Space.selfLogCircleBCF W‖ ≤
      ‖Z.val - W.val‖ * contourLogShapeConstant c M := by
  have hb (θ : ℝ) := norm_contourC1SelfIntegral_sub_le Z.val W.val hc hZ hW hMZ hMW θ
  have hnonneg : 0 ≤ ‖Z.val - W.val‖ * contourLogShapeConstant c M := (norm_nonneg _).trans (hb 0)
  apply (BoundedContinuousFunction.norm_le hnonneg).mpr
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact hb θ

end Euler2D

end
