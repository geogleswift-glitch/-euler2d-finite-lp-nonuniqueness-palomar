module

public import RequestProject.Euler.PlanarBiotSavartWeakDivergence
public import RequestProject.Euler.PlanarKernelIntegrals

/-! The actual singular planar kernel is locally integrable on the
entire plane. Compact smooth spatial convolutions are genuine smooth
bounded kernels for the nonlinear planar particle construction. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff Convolution

namespace Euler2D

theorem locallyIntegrable_planar_kernelK : LocallyIntegrable kernelK volume := by
  apply locallyIntegrable_iff.mpr
  intro C hC
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  have hi : IntegrableOn kernelK (closedBall (0 : R2) (max R 0)) :=
    (integrable_norm_iff measurable_kernelK.aestronglyMeasurable).mp
      (integrableOn_norm_kernelK_closedBall (le_max_right R 0))
  apply hi.mono_set
  intro x hx
  exact mem_closedBall_zero_iff.mpr ((hR x hx).trans (le_max_left R 0))

theorem contDiff_planarKernelVelocity_kernelK {φ : R2 → ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (planarKernelVelocity kernelK φ) :=
  hs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ locallyIntegrable_planar_kernelK

theorem exists_norm_planarKernelVelocity_kernelK_bound {φ : R2 → ℝ}
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ B > 0, ∀ x : R2, ‖planarKernelVelocity kernelK φ x‖ ≤ B := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  have hI : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hs
  let B := max (planarBiotSavartBound φ M) 0 + 1
  refine ⟨B, by dsimp only [B]; linarith [le_max_right (planarBiotSavartBound φ M) 0], ?_⟩
  intro x
  have he := norm_planarKernelVelocity_le_planarBiotSavartBound hI hM (fun z => le_refl ‖kernelK z‖) x
  exact he.trans (by dsimp only [B]; linarith [le_max_left (planarBiotSavartBound φ M) 0])

end Euler2D

end
