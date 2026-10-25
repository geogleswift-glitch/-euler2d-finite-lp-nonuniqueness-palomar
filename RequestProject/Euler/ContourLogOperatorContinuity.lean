module

public import RequestProject.Euler.ContourAdmissibility
public import RequestProject.Euler.ContourEvaluation
public import RequestProject.Euler.ContourLogContinuity

/-!
# Actual logarithmic contour operator on the open chord-regular locus

At every curve with a positive true chord bound, a small ball in the
actual C¹ norm has one common chord bound and common function and
derivative bounds.  Dominated convergence therefore proves continuity
of the literal self-contour integral with the actual derivative.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped Interval NNReal

namespace Euler2D

namespace ContourC1Space

variable {γ : ℝ≥0}

/-- The genuine logarithmic contour operator, using the actual derivative. -/
def selfLogIntegral (f : ContourC1Space γ) (θ : ℝ) : ℂ :=
  contourSelfIntegral (lift γ f) (deriv (lift γ f)) θ

theorem continuousAt_selfLogIntegral_of_positiveChordArc
    (f : ContourC1Space γ) (hf : HasPositiveChordArc f) (θ : ℝ) :
    ContinuousAt (fun q : ContourC1Space γ × ℝ => selfLogIntegral q.1 q.2) (f, θ) := by
  obtain ⟨c, hc, hfc⟩ := hf
  let N : ℝ := ‖f‖ + 1
  let δ : ℝ := min (c / 2) 1
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hnear : ∀ᶠ q : ContourC1Space γ × ℝ in 𝓝 (f, θ), q.1 ∈ Metric.ball f δ :=
    (continuous_fst.tendsto (f, θ)).eventually (Metric.ball_mem_nhds f hδ)
  have hlocal (g : ContourC1Space γ) (hg : g ∈ Metric.ball f δ) :
      HasChordArcLower g (c / 2) ∧ ‖g‖ ≤ N := by
    have hdist : ‖g - f‖ < δ := by
      rw [← _root_.dist_eq_norm g f]
      exact hg
    have hball : g ∈ Metric.ball f (c / 2) := by
      change dist g f < c / 2
      rw [_root_.dist_eq_norm g f]
      exact hdist.trans_le (min_le_left _ _)
    refine ⟨hasChordArcLower_of_mem_ball g f hfc hball, ?_⟩
    calc
      ‖g‖ = ‖(g - f) + f‖ := by congr 1; abel
      _ ≤ ‖g - f‖ + ‖f‖ := _root_.norm_add_le (g - f) f
      _ ≤ N := by dsimp only [N]; linarith [hdist.trans_le (min_le_right (c / 2) 1)]
  have hmeas (q : ContourC1Space γ × ℝ) : AEStronglyMeasurable
      (contourSelfIntegrand (lift γ q.1) (deriv (lift γ q.1)) q.2)
      (volume.restrict (Ι (-π) π)) := by
    have hzτ : Continuous (fun τ : ℝ => lift γ q.1 q.2 - lift γ q.1 (q.2 + τ)) :=
      continuous_const.sub ((contDiff_lift q.1).continuous.comp
        (continuous_const.add continuous_id))
    have hdτ : Continuous (fun τ : ℝ => deriv (lift γ q.1) (q.2 + τ)) :=
      (continuous_deriv_lift_uncurry γ).comp
        (continuous_const.prodMk (continuous_const.add continuous_id))
    exact (hzτ.norm.measurable.log.smul hdτ.measurable).aestronglyMeasurable
  have hangle {τ : ℝ} (hτ : τ ∈ Ι (-π) π) : |τ| ≤ π := by
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -π ≤ π)] at hτ
    exact abs_le.mpr ⟨hτ.1.le, hτ.2⟩
  change ContinuousAt
    (fun q : ContourC1Space γ × ℝ => ∫ τ in (-π)..π,
      contourSelfIntegrand (lift γ q.1) (deriv (lift γ q.1)) q.2 τ) (f, θ)
  refine intervalIntegral.continuousAt_of_dominated_interval
    (Eventually.of_forall hmeas) ?_
    ((intervalIntegrable_contourLogMajorant (c / 2) N).const_mul N) ?_
  · filter_upwards [hnear] with q hq
    have hq' := hlocal q.1 hq
    filter_upwards with τ
    intro hτ
    exact norm_contourSelfIntegrand_le (by positivity : 0 < c / 2)
      (fun t => (norm_eval_le q.1 (t : ContourCircle)).trans hq'.2)
      (fun t => (norm_deriv_lift_le q.1 t).trans hq'.2) hq'.1 q.2 τ (hangle hτ)
  · filter_upwards [volume.ae_ne (0 : ℝ)] with τ hτ
    intro hmem
    have hz : Continuous (fun q : ContourC1Space γ × ℝ => lift γ q.1 q.2) :=
      continuous_lift_uncurry γ
    have hzshift : Continuous (fun q : ContourC1Space γ × ℝ => lift γ q.1 (q.2 + τ)) :=
      hz.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hdshift : Continuous
        (fun q : ContourC1Space γ × ℝ => deriv (lift γ q.1) (q.2 + τ)) :=
      (continuous_deriv_lift_uncurry γ).comp
        (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hn : ‖lift γ f θ - lift γ f (θ + τ)‖ ≠ 0 :=
      ne_of_gt ((mul_pos hc (abs_pos.mpr hτ)).trans_le (hfc θ τ (hangle hmem)))
    have hncont : Continuous
        (fun q : ContourC1Space γ × ℝ => ‖lift γ q.1 q.2 - lift γ q.1 (q.2 + τ)‖) :=
      (hz.sub hzshift).norm
    have hlog : ContinuousAt
        (fun q : ContourC1Space γ × ℝ => Real.log ‖lift γ q.1 q.2 - lift γ q.1 (q.2 + τ)‖)
        (f, θ) := hncont.continuousAt.log hn
    change ContinuousAt (fun q : ContourC1Space γ × ℝ =>
      Real.log ‖lift γ q.1 q.2 - lift γ q.1 (q.2 + τ)‖ • deriv (lift γ q.1) (q.2 + τ)) (f, θ)
    exact hlog.smul hdshift.continuousAt

/-- The genuine operator is jointly continuous on the open locus of
curves with a positive chord bound. -/
theorem continuous_selfLogIntegral_on_positiveChordArc :
    Continuous (fun q : {f : ContourC1Space γ // HasPositiveChordArc f} × ℝ =>
      selfLogIntegral q.1.val q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hi : Continuous
      (fun r : {f : ContourC1Space γ // HasPositiveChordArc f} × ℝ =>
        ((r.1.val : ContourC1Space γ), r.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact ContinuousAt.comp'
    (f := fun r : {f : ContourC1Space γ // HasPositiveChordArc f} × ℝ =>
      ((r.1.val : ContourC1Space γ), r.2)) (x := q)
    (continuousAt_selfLogIntegral_of_positiveChordArc q.1.val q.1.property q.2)
    hi.continuousAt

end ContourC1Space

end Euler2D

end
