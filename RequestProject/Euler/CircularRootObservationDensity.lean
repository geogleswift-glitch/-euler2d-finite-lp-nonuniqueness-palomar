module

public import RequestProject.Euler.CircularActualCapturedInnerMoment
public import RequestProject.Euler.CircularObservedAnnularGeometry

/-! The observed root uses only changes of the contour parameter.
Its enclosed domains therefore give the literal normalized root
vorticity of the same material contour, with no spatial rotation. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] phaseDomainC1_group phaseDomainC1_space

lemma contourRadialFill_littleParameterShift {γ : ℝ≥0} (β : ℝ) (W : LittleContourSpace γ) :
    contourRadialFill (LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ β W)) =
      contourRadialFill (LittleContourSpace.lift γ W) := by
  change contourRadialFill (ContourC1Space.lift γ (contourParameterShiftC1 β W.val)) = _
  exact contourRadialFill_parameterShiftC1 β W.val

theorem observed_root_contourRadialFill_eq_normalized_raw {γ : ℝ≥0}
    (A₀ b R ρ entrance u : ℝ) (X : ℝ → FiniteCircularIndex 0 → LittleContourSpace γ)
    (i : Fin 2) :
    contourRadialFill (LittleContourSpace.lift γ
      (circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u) i)) =
      contourRadialFill (LittleContourSpace.lift γ
        (R⁻¹ • X (physicalTimeFromNormalized (ampScale A₀ b 0) entrance u) (0, i))) := by
  unfold circularCoRotationCLM
  rw [contourParameterShiftFamilyCLM_apply, contourRadialFill_littleParameterShift]
  unfold canonicalPrefixAlignedCurrentCell
  rw [contourParameterShiftFamilyCLM_apply, contourRadialFill_littleParameterShift]
  simp only [canonicalPrefixAbsoluteCell, finiteAncestorAngularVelocity, Fin.sum_univ_zero,
    zero_div, rigidRotationGauge, neg_zero, mul_zero, Complex.ofReal_zero, zero_mul,
    exp_zero, one_smul, normalizedPhysicalCurve, radScale, Fin.val_last, pow_zero, mul_one,
    Pi.smul_apply, Fin.val_zero, show (Fin.last 0 : Fin 1) = 0 by decide]

theorem observed_root_phaseDensity_eq {γ : ℝ≥0}
    (A₀ b R ρ entrance u : ℝ) (hR : 0 < R)
    (X : ℝ → FiniteCircularIndex 0 → LittleContourSpace γ) (x : R2) :
    let t := physicalTimeFromNormalized (ampScale A₀ b 0) entrance u
    let Z := circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u)
    phaseFiniteContourPatchVorticity
      (fun i => finiteCircularInterfaceStrength A₀ b ((0 : Fin 1), i))
      (fun i => (X t (0, i)).val) (centeredComplexHomeomorph.symm x) =
      A₀ * ((5 / 2 : ℝ) * complexDomainIndicator
        (contourRadialFill (LittleContourSpace.lift γ (Z 0))) (normalizedComplexCoordinate R x) -
        (3 / 2 : ℝ) * complexDomainIndicator
        (contourRadialFill (LittleContourSpace.lift γ (Z 1))) (normalizedComplexCoordinate R x)) := by
  dsimp only
  have hpatch (i : Fin 2) :
      complexDomainIndicator
        (contourRadialFill (LittleContourSpace.lift γ
          (circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u) i)))
        (normalizedComplexCoordinate R x) =
      phaseContourPatchVorticity
        (X (physicalTimeFromNormalized (ampScale A₀ b 0) entrance u) (0, i)).val
        (centeredComplexHomeomorph.symm x) := by
    rw [observed_root_contourRadialFill_eq_normalized_raw]
    change phaseContourPatchVorticity
        (R⁻¹ • (X (physicalTimeFromNormalized (ampScale A₀ b 0) entrance u) (0, i)).val)
        (normalizedComplexCoordinate R x) = _
    rw [phaseContourPatchVorticity_smul (inv_ne_zero hR.ne')]
    congr 1
    simp only [normalizedComplexCoordinate, ← complexPhysicalPlane_symm_eq_planeComplexEquiv,
      map_smul, inv_inv, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul, centeredComplexHomeomorph_symm_apply]
  rw [hpatch 0, hpatch 1]
  simp only [phaseFiniteContourPatchVorticity, Fin.sum_univ_two,
    finiteCircularInterfaceStrength, ampScale, Fin.val_zero, pow_zero, div_one,
    circularContourStrengths, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

end Euler2D

end
