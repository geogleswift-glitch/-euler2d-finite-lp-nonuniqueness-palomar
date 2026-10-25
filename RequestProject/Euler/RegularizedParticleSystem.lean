module

public import RequestProject.Euler.RegularizedParticleFlow
public import RequestProject.Euler.RegularizedVelocitySmoothness

/-!
# Existence of the actual smooth-kernel self-consistent particle system

The witnesses come from the Picard solution in bounded displacement space.
Their inverse, area preservation and spatial convolution formula are
conclusions of that construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

/-- Actual paths and their regularized self-consistent velocity, together
with the proved transport and volume identities needed for limiting them. -/
structure SmoothRegularizedParticleSystem (K : R2 → R2) (w : R2 → ℝ)
    (T : ℝ) (L M : ℝ≥0) where
  velocity : ℝ → R2 → R2
  forward : ℝ → R2 → R2
  backward : ℝ → R2 → R2
  bounded : IsBoundedLipschitzVelocity velocity
    (L * particleLabelMass w) (M * particleLabelMass w)
  spatialC1 : IsC1SpatialVelocity velocity
  periodic : ∀ t, IsTorusPeriodic (velocity t)
  divergence_zero : ∀ t x, pd 0 (velocity t) x 0 + pd 1 (velocity t) x 1 = 0
  forward_continuous : Continuous (Function.uncurry forward)
  backward_continuous : Continuous (Function.uncurry backward)
  initial : ∀ a, forward 0 a = a
  derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    HasDerivAt (fun s => forward s a) (velocity t (forward t a)) t
  forward_area : ∀ t ∈ Icc (0 : ℝ) T, TorusAreaPreserving (forward t)
  backward_area : ∀ t, TorusAreaPreserving (backward t)
  forward_lattice : ∀ t a k,
    forward t (a + torusLatticeShift k) = forward t a + torusLatticeShift k
  backward_lattice : ∀ t a k,
    backward t (a + torusLatticeShift k) = backward t a + torusLatticeShift k
  backward_forward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, backward t (forward t a) = a
  forward_backward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, forward t (backward t a) = a
  pushForward : IsVorticityPushForward T w
    (fun t x => w (torusWrap (backward t x))) forward
  label_integral : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    velocity t x = ∫ b, w b • K (x - forward t b + torusCenter) ∂μT
  transported_integral : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    velocity t x = ∫ y, w (torusWrap (backward t y)) • K (x - y + torusCenter) ∂μT

/-- A smooth bounded Lipschitz periodic divergence-free kernel and an
integrable initial density produce the genuine self-consistent system. -/
theorem exists_smoothRegularizedParticleSystem
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hKper : IsTorusPeriodic K)
    (hKdiv : ∀ x, pd 0 K x 0 + pd 1 K x 1 = 0)
    (hw : Integrable w μT) {T : ℝ} (hT : 0 ≤ T) :
    Nonempty (SmoothRegularizedParticleSystem K w T L M) := by
  obtain ⟨η, hη, hη0, hv, _hX, hODE⟩ := exists_regularizedParticle_system hKL hM hw hT
  have hC1 := isC1SpatialVelocity_regularizedLabelVelocity hKC1 hKL hM hw hη
  have hper : ∀ t, IsTorusPeriodic (fun x => regularizedLabelVelocity K w (η t) x) :=
    fun t => isTorusPeriodic_regularizedLabelVelocity hKper w (η t)
  have hdiv : ∀ t x, pd 0 (regularizedLabelVelocity K w (η t)) x 0 +
      pd 1 (regularizedLabelVelocity K w (η t)) x 1 = 0 :=
    fun t x => divergence_regularizedLabelVelocity hKC1 hKL hM hw hKdiv (η t) x
  refine ⟨{
    velocity := fun t x => regularizedLabelVelocity K w (η t) x
    forward := boundedParticleForward hv hT
    backward := boundedParticleBackward hv hT
    bounded := hv
    spatialC1 := hC1
    periodic := hper
    divergence_zero := hdiv
    forward_continuous := boundedParticleForward_continuous hv hT
    backward_continuous := boundedParticleBackward_continuous hv hT
    initial := boundedParticleForward_zero hv hT
    derivative := fun _ ht a => boundedParticleForward_hasDerivAt hv hT ht a
    forward_area := fun _ ht =>
      torusAreaPreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv hper ht
    backward_area := torusAreaPreserving_boundedParticleBackward_all_of_spatialC1
      hv hC1 hT hdiv hper
    forward_lattice := boundedParticleForward_lattice_equivariant hv hT hper
    backward_lattice := boundedParticleBackward_lattice_equivariant hv hT hper
    backward_forward := fun _ ht a => boundedParticleBackward_forward hv hT ht a
    forward_backward := fun _ ht a => boundedParticleForward_backward hv hT ht a
    pushForward := isVorticityPushForward_boundedParticleForward_of_spatialC1
      hv hC1 hT hdiv hper hw
    label_integral := ?_
    transported_integral := fun _ ht x => regularizedLabelVelocity_eq_transported_integral
      hKL hM hKper hw hη hη0 hv hC1 hT hdiv hODE ht x
  }⟩
  intro t ht x
  change (∫ b, w b • K (x - (b + η t b) + torusCenter) ∂μT) =
    ∫ b, w b • K (x - boundedParticleForward hv hT t b + torusCenter) ∂μT
  apply integral_congr_ae
  filter_upwards with b
  rw [← regularizedDisplacement_eq_boundedParticleForward hη hη0 hv hT hODE ht b]

namespace SmoothRegularizedParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
  (S : SmoothRegularizedParticleSystem K w T L M)

theorem memLp_transported {p : ENNReal} (hw : MemLp w p μT) (t : ℝ) :
    MemLp (fun x => w (torusWrap (S.backward t x))) p μT :=
  hw.comp_measurePreserving (S.backward_area t)

theorem eLpNorm_transported {p : ENNReal} (hw : AEStronglyMeasurable w μT) (t : ℝ) :
    eLpNorm (fun x => w (torusWrap (S.backward t x))) p μT = eLpNorm w p μT :=
  eLpNorm_comp_measurePreserving hw (S.backward_area t)

theorem integral_transported (hw : AEStronglyMeasurable w μT) (t : ℝ) :
    (∫ x, w (torusWrap (S.backward t x)) ∂μT) = ∫ x, w x ∂μT := by
  have hm : AEStronglyMeasurable w (Measure.map (torusWrap ∘ S.backward t) μT) := by
    rw [(S.backward_area t).map_eq]
    exact hw
  have hi := integral_map (S.backward_area t).aemeasurable hm
  rw [(S.backward_area t).map_eq] at hi
  exact hi.symm

theorem ae_bound_transported {B : ℝ} (hw : ∀ᵐ x ∂μT, ‖w x‖ ≤ B) (t : ℝ) :
    ∀ᵐ x ∂μT, ‖w (torusWrap (S.backward t x))‖ ≤ B :=
  (S.backward_area t).quasiMeasurePreserving.ae hw

/-- The wrapped inverse identity used in physical-torus transport holds
for the actual inverse maps constructed above. -/
theorem wrapped_inverse {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∀ᵐ a ∂μT, torusWrap (S.backward t (torusWrap (S.forward t a))) = a := by
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
  rw [torusWrap_comp_torusWrap_of_lattice_equivariant (S.backward_lattice t),
    S.backward_forward t ht a]
  exact torusRep_torusProj ha

end SmoothRegularizedParticleSystem

end Euler2D

end
