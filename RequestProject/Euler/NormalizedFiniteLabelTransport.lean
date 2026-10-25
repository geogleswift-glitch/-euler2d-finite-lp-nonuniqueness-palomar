module

public import RequestProject.Euler.NormalizedFiniteParticleHomeomorph
public import RequestProject.Euler.BanachPhysicalTimeSpaceRescaling

/-! The original finite particles transport the same planar initial
label in normalized coordinates. The source identity and the actual
normalized particle derivative are obtained from the same S. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def normalizedPlanarLabelSource (q₀ : R2 → ℝ) (A r t : ℝ) (z : R2) : ℝ :=
  A⁻¹ * q₀ (S.backward t (r • z + torusCenter))

@[simp] theorem normalizedRelativeHomeomorph_symm_apply (r : ℝ) (hr : r ≠ 0) (entrance : ℝ)
    (he : entrance ∈ Icc (0 : ℝ) T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    (S.normalizedRelativeHomeomorph r hr entrance he t ht).symm a =
      r⁻¹ • (S.forward entrance (S.backward t (r • a + torusCenter)) - torusCenter) := rfl

theorem normalizedPlanarLabelSource_transport (q₀ : R2 → ℝ) (A r : ℝ) (hr : r ≠ 0)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (z : R2) :
    S.normalizedPlanarLabelSource q₀ A r t z =
      S.normalizedPlanarLabelSource q₀ A r entrance
        ((S.normalizedRelativeHomeomorph r hr entrance he t ht).symm z) := by
  let H := centeredDilationHomeomorph r hr
  have hH : H ((S.normalizedRelativeHomeomorph r hr entrance he t ht).symm z) =
      S.forward entrance (S.backward t (H z)) := by
    change H (H.symm (S.forward entrance (S.backward t (H z)))) = _
    exact H.apply_symm_apply _
  change A⁻¹ * q₀ (S.backward t (H z)) =
    A⁻¹ * q₀ (S.backward entrance (H ((S.normalizedRelativeHomeomorph r hr entrance he t ht).symm z)))
  rw [hH, S.backward_forward entrance he]

theorem integrable_normalizedPlanarLabelSource (q₀ : R2 → ℝ) (A : ℝ) {r entrance t : ℝ}
    (hr : 0 < r) (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume)
    (hq : Integrable (S.normalizedPlanarLabelSource q₀ A r entrance)) :
    Integrable (S.normalizedPlanarLabelSource q₀ A r t) := by
  let Z := S.normalizedRelativeHomeomorph r hr.ne' entrance he t ht
  have hZ := S.measurePreserving_normalizedRelativeHomeomorph hr he ht hentry htarget
  have hZi : MeasurePreserving Z.symm volume volume := MeasurePreserving.symm Z.toMeasurableEquiv hZ
  apply (hZi.integrable_comp_of_integrable hq).congr
  exact ae_of_all _ (fun z => (S.normalizedPlanarLabelSource_transport q₀ A r hr.ne' entrance he t ht z).symm)

theorem integral_norm_normalizedPlanarLabelSource (q₀ : R2 → ℝ) (A : ℝ) {r entrance t : ℝ}
    (hr : 0 < r) (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume) :
    (∫ z, ‖S.normalizedPlanarLabelSource q₀ A r t z‖) =
      ∫ z, ‖S.normalizedPlanarLabelSource q₀ A r entrance z‖ := by
  let Z := S.normalizedRelativeHomeomorph r hr.ne' entrance he t ht
  have hZ := S.measurePreserving_normalizedRelativeHomeomorph hr he ht hentry htarget
  have hZi : MeasurePreserving Z.symm volume volume := MeasurePreserving.symm Z.toMeasurableEquiv hZ
  have heq := hZi.integral_comp Z.symm.measurableEmbedding
    (fun z => ‖S.normalizedPlanarLabelSource q₀ A r entrance z‖)
  have hs : (fun z => ‖S.normalizedPlanarLabelSource q₀ A r t z‖) =
      fun z => ‖S.normalizedPlanarLabelSource q₀ A r entrance (Z.symm z)‖ := by
    funext z
    rw [S.normalizedPlanarLabelSource_transport q₀ A r hr.ne' entrance he t ht z]
  rw [hs]
  exact heq

theorem norm_normalizedPlanarLabelSource_le (q₀ : R2 → ℝ) (A r : ℝ) (hr : r ≠ 0)
    {entrance t B : ℝ} (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hB : ∀ z, ‖S.normalizedPlanarLabelSource q₀ A r entrance z‖ ≤ B) (z : R2) :
    ‖S.normalizedPlanarLabelSource q₀ A r t z‖ ≤ B := by
  rw [S.normalizedPlanarLabelSource_transport q₀ A r hr entrance he t ht z]
  exact hB _

def normalizedRelativeParticleCurve (A r entrance : ℝ) (a : R2) (τ : ℝ) : R2 :=
  normalizedPhysicalCurve A r entrance
    (fun t => S.forward t (S.backward entrance (r • a + torusCenter)) - torusCenter) τ

theorem normalizedRelativeParticleCurve_eq_homeomorph (A r entrance : ℝ) (hr : r ≠ 0)
    (he : entrance ∈ Icc (0 : ℝ) T) (a : R2) {τ : ℝ}
    (ht : physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T) :
    S.normalizedRelativeParticleCurve A r entrance a τ =
      S.normalizedRelativeHomeomorph r hr entrance he (physicalTimeFromNormalized A entrance τ) ht a := rfl

theorem normalizedRelativeParticleCurve_hasDerivAt (A r entrance : ℝ) (a : R2) {τ : ℝ}
    (ht : physicalTimeFromNormalized A entrance τ ∈ Icc (0 : ℝ) T) :
    HasDerivAt (S.normalizedRelativeParticleCurve A r entrance a)
      ((A * r)⁻¹ • particleVelocityRepresentative f S.backward S.backward_area
        (physicalTimeFromNormalized A entrance τ)
        (S.forward (physicalTimeFromNormalized A entrance τ)
          (S.backward entrance (r • a + torusCenter)))) τ :=
  hasDerivAt_normalizedPhysicalCurve ((S.derivative _ ht _).sub_const torusCenter)

end BoundedEulerParticleSystem
end Euler2D

end
