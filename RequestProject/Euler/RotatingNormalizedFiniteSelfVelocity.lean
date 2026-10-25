module

public import RequestProject.Euler.PlanarVelocityRotatingNormalization
public import RequestProject.Euler.CoupledPlanarBiotSavartAffine

/-! The same transported single label produces its genuine singular
material self velocity in the actual rotating particle coordinates.
The ancestor rigid velocity cancels with the exact frame derivative. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem planarRigidRotation_perpJ (θ : ℝ) (z : R2) :
    planarRigidRotation θ (perpJ z) = perpJ (planarRigidRotation θ z) := by
  have hJ (v : R2) : perpJ v = complexPhysicalPlane (I * complexPhysicalPlane.symm v) := by
    rw [complexPhysicalPlane_mul_I, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = complexPhysicalPlane (Complex.exp ((θ : ℂ) * I) *
        complexPhysicalPlane.symm (complexPhysicalPlane (I * complexPhysicalPlane.symm z))) := by
      rw [hJ z, planarRigidRotation_apply]
    _ = complexPhysicalPlane (I * (Complex.exp ((θ : ℂ) * I) * complexPhysicalPlane.symm z)) := by
      rw [LinearIsometryEquiv.symm_apply_apply]
      congr 1
      ring
    _ = _ := by rw [complexPhysicalPlane_mul_I, planarRigidRotation_apply]

theorem rotating_normalized_rigid_velocity {A r : ℝ} (hA : A ≠ 0) (hr : r ≠ 0)
    (Ω θ : ℝ) (z : R2) :
    planarRigidRotation (-θ) ((A * r)⁻¹ •
      complexPhysicalPlane (((Ω : ℂ) * I) *
        complexPhysicalPlane.symm (r • planarRigidRotation θ z))) = (Ω / A) • perpJ z := by
  have hrigid : complexPhysicalPlane (((Ω : ℂ) * I) *
      complexPhysicalPlane.symm (r • planarRigidRotation θ z)) =
      Ω • perpJ (r • planarRigidRotation θ z) := by
    rw [show ((Ω : ℂ) * I) * complexPhysicalPlane.symm (r • planarRigidRotation θ z) =
      Ω • (I * complexPhysicalPlane.symm (r • planarRigidRotation θ z)) by
        rw [Complex.real_smul]; ring,
      map_smul, complexPhysicalPlane_mul_I, LinearIsometryEquiv.apply_symm_apply]
  rw [hrigid, perpJ_smul]
  simp only [map_smul, smul_smul, planarRigidRotation_perpJ]
  have hcancel : planarRigidRotation (-θ) (planarRigidRotation θ z) = z := by
    simpa only [neg_neg] using planarRigidRotation_neg_cancel (-θ) z
  rw [hcancel]
  congr 1
  field_simp
  <;> ring

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem rotating_normalized_singlePlanar_velocity_eq_material
    (q₀ : R2 → ℝ) (A : ℝ) (hA : A ≠ 0) {r : ℝ} (hr : 0 < r)
    (entrance : ℝ) (he : entrance ∈ Icc (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume)
    (θentry θtarget : ℝ) (z : R2) :
    planarRigidRotation (-θtarget) ((A * r)⁻¹ • complexPhysicalPlane
      (velocityC (fun y => q₀ (S.backward t (complexTorusPoint y)))
        (complexPhysicalPlane.symm (r • planarRigidRotation θtarget z)))) =
      planarMaterialLabelVelocity kernelK
        (S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance)
        (S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht θentry θtarget) z := by
  let u : R2 → ℝ := fun y => q₀ (S.backward t (y + torusCenter))
  have hphysical : complexPhysicalPlane
      (velocityC (fun y => q₀ (S.backward t (complexTorusPoint y)))
        (complexPhysicalPlane.symm (r • planarRigidRotation θtarget z))) =
      planarKernelVelocity kernelK u (r • planarRigidRotation θtarget z) := by
    simpa only [u, complexTorusPoint, LinearIsometryEquiv.apply_symm_apply] using
      complexPhysicalPlane_velocityC (fun y => q₀ (S.backward t (complexTorusPoint y)))
        (r • planarRigidRotation θtarget z)
  rw [hphysical, planarKernelVelocity_rotating_normalization u A hA hr θtarget z]
  have hZ := S.measurePreserving_rotatingNormalizedRelativeHomeomorph hr he ht hentry htarget θentry θtarget
  rw [planarMaterialBiotSavart_eq_spatial _ _ hZ]
  congr 1
  funext y
  change S.rotatingNormalizedPlanarLabelSource q₀ A r θtarget t y =
    S.rotatingNormalizedPlanarLabelSource q₀ A r θentry entrance
      ((S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht θentry θtarget).symm y)
  exact S.rotatingNormalizedPlanarLabelSource_transport q₀ A r hr.ne' entrance he t ht θentry θtarget y

end BoundedEulerParticleSystem
end Euler2D

end
