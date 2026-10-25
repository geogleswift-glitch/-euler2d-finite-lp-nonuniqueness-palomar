module

public import RequestProject.Euler.ComplexPhysicalRotatingFrame
public import RequestProject.Euler.CircularRigidRotationGauge

/-! Physical normalization and the true rigid rotation act on the
original isolated circular field. No replacement field or covariance
hypothesis is introduced. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem hasDerivAt_circularNormalizedPhysicalRotatedCurve {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {A r e τ Ω : ℝ} (hA : A ≠ 0) (hr : r ≠ 0)
    {z p : ℝ → Fin 2 → LittleContourSpace γ}
    (hmem : normalizedPhysicalCurve A r e z τ ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt z
      ((A * r) • circularBanachField hγ hγ1
          (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
        ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) +
        p (physicalTimeFromNormalized A e τ)) (physicalTimeFromNormalized A e τ)) :
    HasDerivAt (fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r e z u)
      (circularBanachField hγ hγ1
          (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) +
        rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ •
          p (physicalTimeFromNormalized A e τ))) τ := by
  exact hasDerivAt_normalizedPhysicalRotatedCurve hA hr hd
    (circularBanachField_complexValueRotation hγ hγ1 ((τ - 0) * (-(Ω / A))) hmem)

theorem norm_circularNormalizedThreeForcing_le {γ : ℝ≥0}
    {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (Ω τ : ℝ)
    (Qa Qi Qt : Fin 2 → LittleContourSpace γ) :
    ‖rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • (Qa + Qi + Qt))‖ ≤
      (‖Qa‖ + ‖Qi‖ + ‖Qt‖) / (A * r) := by
  rw [norm_normalizedPhysicalRotatedForcing hA hr]
  exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) (mul_nonneg hA.le hr.le)

theorem circularNormalizedPhysicalRotatedCurve_mem {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (A r e τ Ω : ℝ) {z : ℝ → Fin 2 → LittleContourSpace γ}
    (hmem : normalizedPhysicalCurve A r e z τ ∈ circularBanachDomain hγ hγ1) :
    rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ ∈
      circularBanachDomain hγ hγ1 :=
  circularRigidRotatedCurve_mem hγ hγ1 (Ω / A) 0 τ hmem

theorem circularNormalizedPhysicalRotatedCurve_initial {γ : ℝ≥0}
    (A r e Ω : ℝ) (z : ℝ → Fin 2 → LittleContourSpace γ) :
    rigidRotationGauge (Ω / A) 0 0 • normalizedPhysicalCurve A r e z 0 = r⁻¹ • z e := by
  rw [rigidRotationGauge_entrance, one_smul, normalizedPhysicalCurve_initial]

end Euler2D

end
