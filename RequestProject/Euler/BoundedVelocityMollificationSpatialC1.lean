module

public import RequestProject.Euler.BoundedVelocityMollification
public import RequestProject.Euler.SpatialC1ParticleFlow

/-! Spatial smoothing has a genuinely jointly continuous spatial
derivative even when the original velocity is only continuous in time. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal Convolution ContDiff

namespace Euler2D

theorem isC1SpatialVelocity_boundedVelocityMollification
    {φ : R2 → ℝ} {v : ℝ → R2 → R2} {M : ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M) :
    IsC1SpatialVelocity (boundedVelocityMollification φ v) := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] R2 →L[ℝ] R2)
  let L' := L.precompL R2
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hi : Integrable (fun y => ‖fderiv ℝ φ y‖) :=
    (hdφ.integrable_of_hasCompactSupport (hs.fderiv ℝ)).norm
  refine ⟨fun t => (contDiff_boundedVelocityMollification hs hφ hv t).differentiable (by simp), ?_⟩
  have he : (fun p : ℝ × R2 => fderiv ℝ (boundedVelocityMollification φ v p.1) p.2) =
      (fun p : ℝ × R2 => ∫ y, L' (fderiv ℝ φ y) (v p.1 (p.2 - y))) := by
    funext p
    have hlocal : LocallyIntegrable (v p.1) volume :=
      (hv.comp ((continuous_const : Continuous (fun _ : R2 => p.1)).prodMk continuous_id)).locallyIntegrable
    exact (hs.hasFDerivAt_convolution_left (μ := volume) (g := v p.1)
      L (hφ.of_le (by simp)) hlocal p.2).fderiv
  rw [he]
  have hb (p : ℝ × R2) (y : R2) :
      ‖L' (fderiv ℝ φ y) (v p.1 (p.2 - y))‖ ≤ (‖L'‖ * M) * ‖fderiv ℝ φ y‖ := by
    calc
      _ ≤ ‖L'‖ * ‖fderiv ℝ φ y‖ * ‖v p.1 (p.2 - y)‖ := L'.le_opNorm₂ _ _
      _ ≤ ‖L'‖ * ‖fderiv ℝ φ y‖ * M := by gcongr; exact hM p.1 _
      _ = _ := by ring
  have hm (p : ℝ × R2) :
      Continuous (fun y => L' (fderiv ℝ φ y) (v p.1 (p.2 - y))) :=
    (L'.continuous.comp hdφ).clm_apply
      (hv.comp (continuous_const.prodMk (continuous_const.sub continuous_id)))
  exact continuous_of_dominated (fun p => (hm p).aestronglyMeasurable)
    (fun p => ae_of_all _ (hb p)) (hi.const_mul (‖L'‖ * M))
    (ae_of_all _ (fun y => (L' (fderiv ℝ φ y)).continuous.comp
      (hv.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)))))

end Euler2D
