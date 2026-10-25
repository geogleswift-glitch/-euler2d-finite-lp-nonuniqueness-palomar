module

public import RequestProject.Euler.ContourCompactDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine smooth dependence of compact-parameter contour integrals

Only smoothness at the actual points of the compact integration strip is
required.  Compactness supplies every local derivative dominator; induction
then gives all finite orders of differentiability of the actual integral.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

namespace Euler2D

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual Fréchet differentiation under integration over a compact real
set, with the bound deduced from joint continuity. -/
theorem hasFDerivAt_setIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) (F : P → ℝ → E) (G : P → ℝ → P →L[ℝ] E)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ S))
    (hderiv : ∀ p u, u ∈ S → HasFDerivAt (fun q => F q u) (G p u) p) (p₀ : P) :
    HasFDerivAt (fun p => ∫ u in S, F p u) (∫ u in S, G p₀ u) p₀ := by
  have hFc (p : P) : ContinuousOn (F p) S :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨mem_univ _, hu⟩)
  have hGc (p : P) : ContinuousOn (G p) S :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨mem_univ _, hu⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hS).exists_bound_of_continuousOn
    (hG.mono (fun _ hp => ⟨mem_univ _, hp.2⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := G) (μ := volume.restrict S) (s := ball p₀ 1) (bound := fun _ => C)
    (ball_mem_nhds p₀ (by norm_num))
    (Eventually.of_forall (fun p => (hFc p).aestronglyMeasurable hS.measurableSet))
    (ContinuousOn.integrableOn_compact hS (hFc p₀))
    ((hGc p₀).aestronglyMeasurable hS.measurableSet)
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p hp
    exact hC (p, u) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le, hu⟩
  · exact integrableOn_const hS.measure_ne_top
  · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
    intro p _
    exact hderiv p u hu

/-- Finite smoothness of the genuine compact-parameter integral.  The
integrand need only be smooth at points of the actual integration strip. -/
theorem contDiff_nat_setIntegral_of_compact {S : Set ℝ} (hS : IsCompact S) (n : ℕ)
    (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q.2 ∈ S → ContDiffAt ℝ n (Function.uncurry F) q) :
    ContDiff ℝ n (fun p => ∫ u in S, F p u) := by
  induction n generalizing E with
  | zero =>
    simp only [Nat.cast_zero] at hF ⊢
    rw [contDiff_zero]
    have hc : ContinuousOn (Function.uncurry F) (univ ×ˢ S) :=
      fun q hq => (hF q hq.2).continuousAt.continuousWithinAt
    -- The continuous compact-parameter theorem uses only the restriction
    -- to the strip; local continuity outside it is not needed.
    apply continuous_iff_continuousAt.mpr
    intro p₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hS).exists_bound_of_continuousOn
      (hc.mono (fun _ hp => ⟨mem_univ _, hp.2⟩))
    apply continuousAt_of_dominated (F := F) (x₀ := p₀)
      (bound := fun _ : ℝ => C) (μ := volume.restrict S)
    · filter_upwards with p
      exact (hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hu => ⟨mem_univ _, hu⟩)).aestronglyMeasurable hS.measurableSet
    · filter_upwards [ball_mem_nhds p₀ (by norm_num : (0 : ℝ) < 1)] with p hp
      filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      exact hC (p, u) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le, hu⟩
    · exact integrableOn_const hS.measure_ne_top
    · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      have hin : ContinuousAt (fun p : P => (p, u)) p₀ :=
        continuousAt_id.prodMk continuousAt_const
      exact (hF (p₀, u) hu).continuousAt.comp (f := fun p : P => (p, u)) (x := p₀) hin
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
    refine ⟨fun p => ∫ u in S, G p u, ih G hG, ?_⟩
    intro p
    exact hasFDerivAt_setIntegral_of_continuousOn_compact hS F G
      (fun q hq => (hF q hq.2).continuousAt.continuousWithinAt)
      (fun q hq => (hG q hq.2).continuousAt.continuousWithinAt) hderiv p

/-- Actual smooth compact integration, without an assumed derivative or
smoothness of the resulting integral. -/
theorem contDiff_setIntegral_of_compact {S : Set ℝ} (hS : IsCompact S)
    (F : P → ℝ → E)
    (hF : ∀ q : P × ℝ, q.2 ∈ S → ContDiffAt ℝ ∞ (Function.uncurry F) q) :
    ContDiff ℝ ∞ (fun p => ∫ u in S, F p u) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_setIntegral_of_compact hS n F
    (fun q hq => (hF q hq).of_le (WithTop.coe_le_coe.mpr le_top))

end Euler2D

end
