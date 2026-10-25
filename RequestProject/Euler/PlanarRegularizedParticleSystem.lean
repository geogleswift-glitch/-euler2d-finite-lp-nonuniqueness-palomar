module

public import RequestProject.Euler.RegularizedParticleSystem
public import RequestProject.Euler.PlanarLogParticleFlow

/-! The actual Picard construction also gives a genuine planar
self-consistent smooth-kernel particle system. The source box is only
the finite initial-label integration domain; the material maps and
their volume preservation are on the entire Euclidean plane. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

structure SmoothPlanarRegularizedParticleSystem (K : R2 → R2) (w : R2 → ℝ)
    (T : ℝ) (L M : ℝ≥0) where
  velocity : ℝ → R2 → R2
  particles : PlanarLogParticleFlow velocity T
  bounded : IsBoundedLipschitzVelocity velocity (L * particleLabelMass w) (M * particleLabelMass w)
  spatialC1 : IsC1SpatialVelocity velocity
  divergence_zero : ∀ t x, pd 0 (velocity t) x 0 + pd 1 (velocity t) x 1 = 0
  forward_area : ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (particles.forward t) volume volume
  backward_area : ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (particles.backward t) volume volume
  label_integral : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    velocity t x = ∫ b, w b • K (x - particles.forward t b) ∂μT

theorem exists_smoothPlanarRegularizedParticleSystem
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hKdiv : ∀ x, pd 0 K x 0 + pd 1 K x 1 = 0)
    (hw : Integrable w μT) {T : ℝ} (hT : 0 ≤ T) :
    Nonempty (SmoothPlanarRegularizedParticleSystem K w T L M) := by
  let J : R2 → R2 := fun x => K (x - torusCenter)
  have hJC1 : ContDiff ℝ 1 J := hKC1.comp (contDiff_id.sub contDiff_const)
  have hJL : LipschitzWith L J := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := hKL.dist_le_mul (x - torusCenter) (y - torusCenter)
    simpa only [dist_sub_right] using he
  have hJM (x : R2) : ‖J x‖ ≤ M := hM _
  have hJpd (i : Fin 2) (x : R2) : pd i J x = pd i K (x - torusCenter) := by
    unfold pd
    change (fderiv ℝ (fun y => K (y + -torusCenter)) x) _ = _
    rw [fderiv_comp_add_right]
    rfl
  have hJdiv (x : R2) : pd 0 J x 0 + pd 1 J x 1 = 0 := by
    rw [hJpd, hJpd]
    exact hKdiv _
  obtain ⟨η, hη, hη0, hv, hXc, hODE⟩ := exists_regularizedParticle_system hJL hJM hw hT
  have hC1 := isC1SpatialVelocity_regularizedLabelVelocity hJC1 hJL hJM hw hη
  have hdiv : ∀ t x, pd 0 (regularizedLabelVelocity J w (η t)) x 0 +
      pd 1 (regularizedLabelVelocity J w (η t)) x 1 = 0 :=
    fun t x => divergence_regularizedLabelVelocity hJC1 hJL hJM hw hJdiv (η t) x
  let P : PlanarLogParticleFlow (fun t x => regularizedLabelVelocity J w (η t) x) T := {
    forward := boundedParticleForward hv hT
    backward := boundedParticleBackward hv hT
    continuous_forward := boundedParticleForward_continuous hv hT
    continuous_backward := boundedParticleBackward_continuous hv hT
    initial := boundedParticleForward_zero hv hT
    derivative := fun t ht a => boundedParticleForward_hasDerivAt hv hT ht a
    left_inv := fun t ht a => boundedParticleBackward_forward hv hT ht a
    right_inv := fun t ht a => boundedParticleForward_backward hv hT ht a
  }
  refine ⟨{
    velocity := fun t x => regularizedLabelVelocity J w (η t) x
    particles := P
    bounded := hv
    spatialC1 := hC1
    divergence_zero := hdiv
    forward_area := fun t ht => measurePreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv ht
    backward_area := fun t ht => measurePreserving_boundedParticleBackward_of_spatialC1 hv hC1 hT hdiv ht
    label_integral := ?_
  }⟩
  intro t ht x
  unfold regularizedLabelVelocity
  apply integral_congr_ae
  exact ae_of_all _ (fun b => by
    change w b • J (x - (b + η t b) + torusCenter) = w b • K (x - boundedParticleForward hv hT t b)
    rw [← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht b]
    dsimp only [J]
    rw [add_sub_cancel_right])

end Euler2D

end
