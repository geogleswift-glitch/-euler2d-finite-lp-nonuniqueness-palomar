module

public import RequestProject.Euler.ContourCauchyOperator
public import RequestProject.Euler.ContourCauchyIncrementContinuity
public import RequestProject.Euler.ContourAdmissibility
public import RequestProject.Euler.ContourEvaluation

/-! # Actual continuity of the Cauchy increment on the positive chord locus -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped NNReal Interval

namespace Euler2D

private lemma norm_le_norm_add_one_of_mem_ball {E : Type*} [NormedAddCommGroup E]
    (x y : E) (h : x ∈ Metric.ball y 1) : ‖x‖ ≤ ‖y‖ + 1 := by
  have hd : ‖x - y‖ < 1 := by
    rw [← _root_.dist_eq_norm x y]
    exact h
  linarith [norm_sub_norm_le x y]

theorem continuousAt_contourC1CauchyIncrement_of_positiveChordArc {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ) (hZ : ContourC1Space.HasPositiveChordArc Z)
    (f : ContourHolderSpace γ) (θ : ℝ) :
    ContinuousAt (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
      contourC1CauchyIncrement q.1.1 q.1.2 q.2) ((Z, f), θ) := by
  obtain ⟨c, hc, hZc⟩ := hZ
  let NZ : ℝ := ‖Z‖ + 1
  let Nf : ℝ := ‖f‖ + 1
  let δ : ℝ := min (c / 2) 1
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hnearZ : ∀ᶠ q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ in 𝓝 ((Z, f), θ),
      q.1.1 ∈ Metric.ball Z δ :=
    ((continuous_fst.comp continuous_fst).tendsto ((Z, f), θ)).eventually
      (Metric.ball_mem_nhds Z hδ)
  have hnearf : ∀ᶠ q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ in 𝓝 ((Z, f), θ),
      q.1.2 ∈ Metric.ball f 1 :=
    ((continuous_snd.comp continuous_fst).tendsto ((Z, f), θ)).eventually
      (Metric.ball_mem_nhds f (by norm_num))
  have hlocalZ (W : ContourC1Space γ) (hW : W ∈ Metric.ball Z δ) :
      ContourC1Space.HasChordArcLower W (c / 2) ∧ ‖W‖ ≤ NZ := by
    have hd : dist W Z < δ := hW
    have hball : W ∈ Metric.ball Z (c / 2) := hd.trans_le (min_le_left _ _)
    have hball1 : W ∈ Metric.ball Z 1 := hd.trans_le (min_le_right _ _)
    exact ⟨ContourC1Space.hasChordArcLower_of_mem_ball W Z hZc hball,
      norm_le_norm_add_one_of_mem_ball W Z hball1⟩
  have hmeas (q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ) : AEStronglyMeasurable
      (contourC1CauchyIncrementIntegrand q.1.1 q.1.2 q.2)
      (volume.restrict (Icc (-π) π)) := by
    exact (measurable_contourCauchyIncrementIntegrand
      (ContourC1Space.contDiff_lift q.1.1).continuous.measurable
      (measurable_contourC1_lift_deriv q.1.1)
      (((HolderFunctionSpace.toBCF γ q.1.2).continuous.comp
        (AddCircle.continuous_mk' (2 * π))).measurable) q.2).aestronglyMeasurable
  change ContinuousAt (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
    ∫ τ in Icc (-π) π, contourC1CauchyIncrementIntegrand q.1.1 q.1.2 q.2 τ) ((Z, f), θ)
  refine continuousAt_of_dominated (bound := fun τ => (NZ * Nf / (c / 2)) * |τ| ^ ((γ : ℝ) - 1))
    (Eventually.of_forall hmeas) ?_
    ((integrableOn_abs_rpow_sub_one hγ Real.pi_pos.le).const_mul _) ?_
  · filter_upwards [hnearZ, hnearf] with q hqZ hqf
    have hW := hlocalZ q.1.1 hqZ
    have hF : ‖q.1.2‖ ≤ Nf := norm_le_norm_add_one_of_mem_ball q.1.2 f hqf
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    apply norm_contourCauchyIncrementIntegrand_le (by positivity : 0 < c / 2)
      (by dsimp [NZ]; positivity) (by dsimp [Nf]; positivity)
    · exact hW.1 q.2 τ (abs_le.mpr hτ)
    · exact (ContourC1Space.norm_deriv_lift_le q.1.1 (q.2 + τ)).trans hW.2
    · exact (norm_contourHolder_lift_sub_le q.1.2 q.2 τ).trans
        (mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg (abs_nonneg τ) _))
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with τ hτ hτ0
    have hz : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        ContourC1Space.lift γ q.1.1 q.2) :=
      (ContourC1Space.continuous_lift_uncurry γ).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hd : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        deriv (ContourC1Space.lift γ q.1.1) q.2) :=
      (ContourC1Space.continuous_deriv_lift_uncurry γ).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hF : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        q.1.2 (q.2 : ContourCircle)) :=
      (HolderFunctionSpace.continuous_eval_uncurry (X := ContourCircle) (E := ℂ) γ).comp
        ((continuous_snd.comp continuous_fst).prodMk
          ((AddCircle.continuous_mk' (2 * π)).comp continuous_snd))
    have hshift : Continuous
        (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ => (q.1, q.2 + τ)) :=
      continuous_fst.prodMk (continuous_snd.add continuous_const)
    have hzshift : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        ContourC1Space.lift γ q.1.1 (q.2 + τ)) := hz.comp hshift
    have hdshift : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        deriv (ContourC1Space.lift γ q.1.1) (q.2 + τ)) := hd.comp hshift
    have hfshift : Continuous (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        q.1.2 ((q.2 + τ : ℝ) : ContourCircle)) := hF.comp hshift
    have hn : ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ) ≠ 0 :=
      norm_pos_iff.mp ((mul_pos hc (abs_pos.mpr hτ0)).trans_le
        (hZc θ τ (abs_le.mpr hτ)))
    have hquot : ContinuousAt
        (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
          deriv (ContourC1Space.lift γ q.1.1) (q.2 + τ) /
            (ContourC1Space.lift γ q.1.1 q.2 - ContourC1Space.lift γ q.1.1 (q.2 + τ)))
        ((Z, f), θ) := hdshift.continuousAt.div (hz.sub hzshift).continuousAt hn
    change ContinuousAt
      (fun q : (ContourC1Space γ × ContourHolderSpace γ) × ℝ =>
        (deriv (ContourC1Space.lift γ q.1.1) (q.2 + τ) /
          (ContourC1Space.lift γ q.1.1 q.2 - ContourC1Space.lift γ q.1.1 (q.2 + τ))) *
            (q.1.2 ((q.2 + τ : ℝ) : ContourCircle) - q.1.2 (q.2 : ContourCircle))) ((Z, f), θ)
    exact hquot.mul (hfshift.sub hF).continuousAt

theorem continuous_contourC1CauchyIncrement_on_positiveChordArc {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) :
    Continuous (fun q : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
        ContourHolderSpace γ) × ℝ => contourC1CauchyIncrement q.1.1.val q.1.2 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hi : Continuous
      (fun p : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
          ContourHolderSpace γ) × ℝ => ((p.1.1.val, p.1.2), p.2)) :=
    (((continuous_subtype_val.comp continuous_fst).comp continuous_fst).prodMk
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  exact ContinuousAt.comp'
    (f := fun p : ({Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
      ContourHolderSpace γ) × ℝ => ((p.1.1.val, p.1.2), p.2)) (x := q)
    (continuousAt_contourC1CauchyIncrement_of_positiveChordArc hγ
      q.1.1.val q.1.1.property q.1.2 q.2) hi.continuousAt

end Euler2D

end
