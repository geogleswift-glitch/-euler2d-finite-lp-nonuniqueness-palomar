module

public import RequestProject.Euler.RegularizedParticleSystem

/-! The same genuine smooth torus particle maps also preserve
infinite planar volume. This property is retained before taking
the joint forward/inverse limit. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D
namespace SmoothRegularizedParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem K w T L M)

theorem forward_eq_boundedParticleForward (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    S.forward t a = boundedParticleForward S.bounded hT t a := by
  have hSc : Continuous (fun s => S.forward s a) :=
    S.forward_continuous.comp (continuous_id.prodMk continuous_const)
  have hBc : Continuous (fun s => boundedParticleForward S.bounded hT s a) :=
    (boundedParticleForward_continuous S.bounded hT).comp (continuous_id.prodMk continuous_const)
  have he := ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun s _ => (S.bounded.lipschitz s).lipschitzOnWith)
    hSc.continuousOn
    (fun s hs => (S.derivative s ⟨hs.1, hs.2.le⟩ a).hasDerivWithinAt)
    (fun _ _ => trivial)
    hBc.continuousOn
    (fun s hs => (boundedParticleForward_hasDerivAt S.bounded hT ⟨hs.1, hs.2.le⟩ a).hasDerivWithinAt)
    (fun _ _ => trivial)
    (by rw [S.initial, boundedParticleForward_zero])
  exact he ht

theorem planar_area (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (S.forward t) volume volume ∧ MeasurePreserving (S.backward t) volume volume := by
  have hforward : MeasurePreserving (S.forward t) volume volume := by
    have he : S.forward t = boundedParticleForward S.bounded hT t :=
      funext (S.forward_eq_boundedParticleForward hT ht)
    rw [he]
    exact measurePreserving_boundedParticleForward_of_spatialC1 S.bounded S.spatialC1 hT S.divergence_zero ht
  let H : R2 ≃ₜ R2 := {
    toFun := S.forward t
    invFun := S.backward t
    left_inv := S.backward_forward t ht
    right_inv := S.forward_backward t ht
    continuous_toFun := S.forward_continuous.comp (continuous_const.prodMk continuous_id)
    continuous_invFun := S.backward_continuous.comp (continuous_const.prodMk continuous_id)
  }
  exact ⟨hforward, MeasurePreserving.symm H.toMeasurableEquiv hforward⟩

end SmoothRegularizedParticleSystem
end Euler2D

end
