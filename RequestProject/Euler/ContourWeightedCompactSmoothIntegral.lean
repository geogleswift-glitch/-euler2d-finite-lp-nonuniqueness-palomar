module

public import RequestProject.Euler.ContourCompactSmoothIntegral

/-! A fixed genuine integrable scalar weight may be singular in the
integration parameter.  Actual compact derivative bounds still give
smoothness in the external parameter. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

namespace Euler2D

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integrableOn_smul_continuousOn_compact {S : Set ℝ} (hS : IsCompact S)
    {w : ℝ → ℝ} (hw : IntegrableOn w S) {f : ℝ → E} (hf : ContinuousOn f S) :
    IntegrableOn (fun u => w u • f u) S := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  apply (hw.norm.const_mul C).mono'
    (hw.aestronglyMeasurable.smul (hf.aestronglyMeasurable hS.measurableSet))
  filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
  rw [Pi.smul_apply', norm_smul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)

theorem hasFDerivAt_weightedSetIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    (F : P → ℝ → E) (G : P → ℝ → P →L[ℝ] E)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ S))
    (hderiv : ∀ p u, u ∈ S → HasFDerivAt (fun q => F q u) (G p u) p) (p₀ : P) :
    HasFDerivAt (fun p => ∫ u in S, w u • F p u) (∫ u in S, w u • G p₀ u) p₀ := by
  have hFc (p : P) : ContinuousOn (F p) S :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨mem_univ _, hu⟩)
  have hGc (p : P) : ContinuousOn (G p) S :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨mem_univ _, hu⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hS).exists_bound_of_continuousOn
    (hG.mono (fun _ hp => ⟨mem_univ _, hp.2⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p u => w u • F p u) (F' := fun p u => w u • G p u)
    (μ := volume.restrict S) (s := ball p₀ 1) (bound := fun u => C * ‖w u‖)
    (ball_mem_nhds p₀ (by norm_num))
    (Eventually.of_forall (fun p => hw.aestronglyMeasurable.smul
      ((hFc p).aestronglyMeasurable hS.measurableSet)))
    (integrableOn_smul_continuousOn_compact hS hw (hFc p₀))
    (hw.aestronglyMeasurable.smul ((hGc p₀).aestronglyMeasurable hS.measurableSet))
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p hp
    rw [norm_smul, mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (hC (p, u) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le, hu⟩) (norm_nonneg _)
  · exact hw.norm.const_mul C
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p _
    exact (hderiv p u hu).const_smul (w u)

theorem contDiff_nat_weightedSetIntegral_of_compact {S : Set ℝ} (hS : IsCompact S)
    {w : ℝ → ℝ} (hw : IntegrableOn w S) (n : ℕ) (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q.2 ∈ S → ContDiffAt ℝ n (Function.uncurry F) q) :
    ContDiff ℝ n (fun p => ∫ u in S, w u • F p u) := by
  induction n generalizing E with
  | zero =>
    simp only [Nat.cast_zero] at hF ⊢
    rw [contDiff_zero]
    have hc : ContinuousOn (Function.uncurry F) (univ ×ˢ S) :=
      fun q hq => (hF q hq.2).continuousAt.continuousWithinAt
    apply continuous_iff_continuousAt.mpr
    intro p₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hS).exists_bound_of_continuousOn
      (hc.mono (fun _ hp => ⟨mem_univ _, hp.2⟩))
    apply continuousAt_of_dominated (F := fun p u => w u • F p u) (x₀ := p₀)
      (bound := fun u => C * ‖w u‖) (μ := volume.restrict S)
    · filter_upwards with p
      exact hw.aestronglyMeasurable.smul
        ((hc.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun _ hu => ⟨mem_univ _, hu⟩)).aestronglyMeasurable hS.measurableSet)
    · filter_upwards [ball_mem_nhds p₀ (by norm_num : (0 : ℝ) < 1)] with p hp
      filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left
        (hC (p, u) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le, hu⟩) (norm_nonneg _)
    · exact hw.norm.const_mul C
    · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      have hin : ContinuousAt (fun p : P => (p, u)) p₀ :=
        continuousAt_id.prodMk continuousAt_const
      exact ((hF (p₀, u) hu).continuousAt.comp
        (f := fun p : P => (p, u)) (x := p₀) hin).const_smul (w u)
  | succ n ih =>
    let G : P → ℝ → P →L[ℝ] E := fun p u =>
      (fderiv ℝ (Function.uncurry F) (p, u)).comp (ContinuousLinearMap.inl ℝ P ℝ)
    have hG (q : P × ℝ) (hq : q.2 ∈ S) :
        ContDiffAt ℝ n (Function.uncurry G) q := by
      exact ((hF q hq).fderiv_right (by norm_cast)).clm_comp contDiffAt_const
    have hderiv (p : P) (u : ℝ) (hu : u ∈ S) :
        HasFDerivAt (fun q => F q u) (G p u) p := by
      have hd := ((hF (p, u) hu).differentiableAt (by simp)).hasFDerivAt
      have hin : HasFDerivAt (fun q : P => (q, u)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
        (hasFDerivAt_id p).prodMk (hasFDerivAt_const u p)
      exact hd.comp p hin
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun p => ∫ u in S, w u • G p u, ih G hG, ?_⟩
    intro p
    exact hasFDerivAt_weightedSetIntegral_of_continuousOn_compact hS hw F G
      (fun q hq => (hF q hq.2).continuousAt.continuousWithinAt)
      (fun q hq => (hG q hq.2).continuousAt.continuousWithinAt) hderiv p

theorem contDiff_weightedSetIntegral_of_compact {S : Set ℝ} (hS : IsCompact S)
    {w : ℝ → ℝ} (hw : IntegrableOn w S) (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q.2 ∈ S → ContDiffAt ℝ ∞ (Function.uncurry F) q) :
    ContDiff ℝ ∞ (fun p => ∫ u in S, w u • F p u) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_weightedSetIntegral_of_compact hS hw n F
    (fun q hq => (hF q hq).of_le (WithTop.coe_le_coe.mpr le_top))

end Euler2D

end
