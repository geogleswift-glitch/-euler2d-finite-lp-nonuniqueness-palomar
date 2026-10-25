module

public import RequestProject.Euler.RegularizedParticleExistence
public import RequestProject.Euler.SpatialC1ParticleFlow
public import RequestProject.Euler.TorusFlowVolume

/-!
# The actual self-consistent displacement flow and transported labels

ODE uniqueness identifies the Banach-space construction with the actual
two-time particle flow.  Its inverse and area preservation then follow
from the already proved variational and change-of-variables arguments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

/-- Uniqueness identifies an actual displacement-space solution with
the previously constructed particle flow of its actual integral driver. -/
theorem regularizedDisplacement_eq_boundedParticleForward
    {K : R2 → R2} {w : R2 → ℝ} {η : ℝ → ParticleDisplacement}
    {L M : ℝ≥0} (hη : Continuous η) (hη0 : η 0 = 0)
    (hv : IsBoundedLipschitzVelocity
      (fun t x => regularizedLabelVelocity K w (η t) x) L M)
    {T : ℝ} (hT : 0 ≤ T)
    (hODE : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : R2,
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    a + η t a = boundedParticleForward hv hT t a := by
  have hc : Continuous (fun s => a + η s a) :=
    continuous_const.add (hη.eval continuous_const)
  have hbc : Continuous (fun s => boundedParticleForward hv hT s a) :=
    (boundedParticleForward_continuous hv hT).comp
      (continuous_id.prodMk continuous_const)
  have he := ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun s hs => (hv.lipschitz s).lipschitzOnWith)
    hc.continuousOn
    (fun s hs => (hODE s ⟨hs.1, hs.2.le⟩ a).hasDerivWithinAt)
    (fun _ _ => trivial)
    hbc.continuousOn
    (fun s hs => (boundedParticleForward_hasDerivAt hv hT ⟨hs.1, hs.2.le⟩ a).hasDerivWithinAt)
    (fun _ _ => trivial)
    (by simp [hη0])
  exact he ht

theorem torusAreaPreserving_boundedParticleForward_of_spatialC1
    {v : ℝ → R2 → R2} {L M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v L M) (hC1 : IsC1SpatialVelocity v)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    TorusAreaPreserving (boundedParticleForward hv hT t) :=
  torusAreaPreserving_of_measurePreserving_lattice_equivariant
    (measurePreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv ht)
    (boundedParticleForward_lattice_equivariant hv hT hper t)

theorem torusAreaPreserving_boundedParticleBackward_of_spatialC1
    {v : ℝ → R2 → R2} {L M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v L M) (hC1 : IsC1SpatialVelocity v)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    TorusAreaPreserving (boundedParticleBackward hv hT t) :=
  torusAreaPreserving_of_measurePreserving_lattice_equivariant
    (measurePreserving_boundedParticleBackward_of_spatialC1 hv hC1 hT hdiv ht)
    (boundedParticleBackward_lattice_equivariant hv hT hper t)

theorem torusAreaPreserving_boundedParticleBackward_all_of_spatialC1
    {v : ℝ → R2 → R2} {L M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v L M) (hC1 : IsC1SpatialVelocity v)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) (t : ℝ) :
    TorusAreaPreserving (boundedParticleBackward hv hT t) := by
  let τ := projIcc 0 T hT t
  have he : boundedParticleBackward hv hT t = boundedParticleBackward hv hT (τ : ℝ) := by
    funext a
    unfold boundedParticleBackward
    rw [projIcc_of_mem hT τ.property]
  rw [he]
  exact torusAreaPreserving_boundedParticleBackward_of_spatialC1 hv hC1 hT hdiv hper τ.property

theorem isVorticityPushForward_boundedParticleForward_of_spatialC1
    {v : ℝ → R2 → R2} {L M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v L M) (hC1 : IsC1SpatialVelocity v)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {w : R2 → ℝ} (hw : Integrable w μT) :
    IsVorticityPushForward T w
      (fun t x => w (torusWrap (boundedParticleBackward hv hT t x)))
      (boundedParticleForward hv hT) := by
  apply IsVorticityPushForward.of_torusInverse hw
    (fun _ ht => torusAreaPreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv hper ht)
    (fun _ ht => torusAreaPreserving_boundedParticleBackward_of_spatialC1 hv hC1 hT hdiv hper ht)
  intro t ht
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
  rw [torusWrap_comp_torusWrap_of_lattice_equivariant
    (boundedParticleBackward_lattice_equivariant hv hT hper t),
    boundedParticleBackward_forward hv hT ht]
  exact torusRep_torusProj ha

/-- The self-consistent label integral is the actual spatial convolution
with the density transported by the inverse particle map. -/
theorem regularizedLabelVelocity_eq_transported_integral
    {K : R2 → R2} {w : R2 → ℝ} {η : ℝ → ParticleDisplacement}
    {L₀ M₀ L M : ℝ≥0}
    (hK : LipschitzWith L₀ K) (hM : ∀ x, ‖K x‖ ≤ M₀)
    (hKper : IsTorusPeriodic K) (hw : Integrable w μT)
    (hη : Continuous η) (hη0 : η 0 = 0)
    (hv : IsBoundedLipschitzVelocity
      (fun t x => regularizedLabelVelocity K w (η t) x) L M)
    (hC1 : IsC1SpatialVelocity (fun t x => regularizedLabelVelocity K w (η t) x))
    {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (regularizedLabelVelocity K w (η t)) x 0 +
      pd 1 (regularizedLabelVelocity K w (η t)) x 1 = 0)
    (hODE : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : R2,
      HasDerivAt (fun s => a + η s a)
        (regularizedLabelVelocity K w (η t) (a + η t a)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    regularizedLabelVelocity K w (η t) x =
      ∫ y, w (torusWrap (boundedParticleBackward hv hT t y)) •
        K (x - y + torusCenter) ∂μT := by
  have hper : ∀ s, IsTorusPeriodic (fun x => regularizedLabelVelocity K w (η s) x) :=
    fun s => isTorusPeriodic_regularizedLabelVelocity hKper w (η s)
  have hp := isVorticityPushForward_boundedParticleForward_of_spatialC1
    hv hC1 hT hdiv hper hw
  have hil := RegularizedParticleConstruction.integrable_label_integrand hK hM hw (η t) x
  have hir : Integrable (fun y => w (torusWrap (boundedParticleBackward hv hT t y)) •
      K (x - y + torusCenter)) μT := by
    simpa using
      RegularizedParticleConstruction.integrable_label_integrand hK hM (hp.integrable t ht)
        (0 : ParticleDisplacement) x
  have htestper : IsTorusPeriodic (fun y => K (x - y + torusCenter)) := by
    intro y i
    have he : x - (y + EuclideanSpace.single i (2 * Real.pi)) + torusCenter +
        EuclideanSpace.single i (2 * Real.pi) = x - y + torusCenter := by abel
    calc
      _ = K (x - (y + EuclideanSpace.single i (2 * Real.pi)) + torusCenter +
          EuclideanSpace.single i (2 * Real.pi)) := (hKper _ i).symm
      _ = _ := congrArg K he
  ext j
  have hleft := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm hil
  have hright := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm hir
  simp only [PiLp.proj_apply] at hleft hright
  have hpair := hp.pairing t ht (fun y => K (x - y + torusCenter) j)
    ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
      (hK.continuous.comp ((continuous_const.sub continuous_id).add continuous_const)))
    (fun y i => congrArg (fun z : R2 => z j) (htestper y i))
  have hpos (a : R2) := regularizedDisplacement_eq_boundedParticleForward
    hη hη0 hv hT hODE ht a
  change (∫ b, w b • K (x - (b + η t b) + torusCenter) ∂μT) j = _
  rw [← hleft, ← hright]
  simpa only [PiLp.smul_apply, smul_eq_mul, ← hpos] using hpair.symm

end Euler2D

end
