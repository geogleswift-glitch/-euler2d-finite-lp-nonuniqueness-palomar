module

public import RequestProject.Euler.RegularizedParticleSystem
public import RequestProject.Euler.TorusKernelMollification

/-!
# Self-consistent systems for the actual regularized torus kernel

This specializes the construction to the previously constructed smooth
Biot--Savart kernel regularization.  No kernel or particle existence is
an additional hypothesis of this result.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Euler2D

theorem exists_regularizedTorusParticleSystem
    {w : R2 → ℝ} (hw : Integrable w μT) {T : ℝ} (hT : 0 ≤ T)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ≥0, Nonempty
      (SmoothRegularizedParticleSystem (regularizedTorusKernel ε hε) w T C C) := by
  obtain ⟨C, hM, _hD, hL⟩ := regularizedTorusKernel_bounds hε hε1
  refine ⟨C, exists_smoothRegularizedParticleSystem
    ((regularizedTorusKernel_smooth hε hε1).of_le (by simp)) hL hM
    (regularizedTorusKernel_periodic ε hε) (regularizedTorusKernel_divergence hε hε1) hw hT⟩

end Euler2D

end
