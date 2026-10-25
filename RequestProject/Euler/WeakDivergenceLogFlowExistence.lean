module

public import RequestProject.Euler.PlanarLogFlowMeasure
public import RequestProject.Euler.BoundedLogVelocityApproximation
public import RequestProject.Euler.BoundedVelocityMollificationSpatialC1
public import RequestProject.Euler.PlanarWeakDivergenceMollification

/-! A bounded continuous velocity with a common logarithmic spatial
modulus and actual weak zero divergence has a true area-preserving
planar particle flow. Smooth divergence-free approximations are built. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_measurePreserving_weakDivergence_logFlow
    {v : ℝ → R2 → R2} {M C : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (hlog : ∀ t x y, ‖x - y‖ ≤ 1 / 2 → ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖)
    (hdiv : ∀ t, IsPlanarWeaklyDivergenceFree (v t)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : PlanarLogParticleFlow v T, ∀ t ∈ Icc (0 : ℝ) T,
      MeasurePreserving (S.forward t) volume volume ∧ MeasurePreserving (S.backward t) volume volume := by
  obtain ⟨K, hK, hs, hmod, hconv⟩ := exists_smoothBoundedLogVelocityApproximation hv hM hlog
  apply exists_measurePreserving_planarLogParticleFlow hv
    (smoothBoundedLogVelocityApproximation v) K M C hK hmod hconv _ _ hT
  · intro n
    exact isC1SpatialVelocity_boundedVelocityMollification (planarVelocityMollifier_compact _)
      (planarVelocityMollifier_smooth _) hv hM
  · intro n t x
    exact divergence_boundedVelocityMollification_zero (planarVelocityMollifier_compact _)
      (planarVelocityMollifier_smooth _) hv hdiv t x

end Euler2D

end
