module

public import RequestProject.Euler.CircularNormalFourierIdentity

/-! The normal Fourier identity along the actual circular material orbit.
The field and derivative are the original little Banach field throughout. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) orbitNormalC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) orbitNormalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) orbitNormalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem littleCircularMaterialContours_eq_shift {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    littleCircularMaterialContours hγ hγ1 t =
      contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
        (littleCircularReference hγ hγ1) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 t i) θ =
    LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (circularContourAngularVelocities i * t)
        (littleCircularReference hγ hγ1 i)) θ
  rw [lift_littleCircularMaterialContours, lift_contourParameterShiftLittleCLM]
  rfl

set_option maxHeartbeats 800000 in
theorem fderiv_circularBanachField_material_orbit {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (t : ℝ) (H : Fin 2 → LittleContourSpace γ) :
    fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
        (contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t) H) =
      contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H) := by
  let Z : AdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii :=
    ⟨littleCircularReference hγ hγ1, admissible_littleCircularReference hγ hγ1⟩
  let hr : ∀ i : Fin 2, 0 < circularContourRadii i :=
    fun i => by fin_cases i <;> simp [circularContourRadii, cellA_pos]
  have hzero := fderiv_finiteContourPhaseFieldTotal_conjugate hγ hγ1
    (circularReferenceC1 hγ hγ1) circularContourRadii hr
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z 0 H
  simp only [contourParameterShiftFamilyCLM_zero] at hzero
  rw [littleCircularMaterialContours_eq_shift]
  have hphase := fderiv_finiteContourPhaseFieldTotal_conjugate hγ hγ1
    (circularReferenceC1 hγ hγ1) circularContourRadii hr
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z
    (fun i => circularContourAngularVelocities i * t) H
  exact hphase.trans (congrArg
    (contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)) hzero.symm)

set_option maxHeartbeats 800000 in
theorem circularOrbitNormalFourierIdentity {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (η τ : Fin 2 → ℂ)
    (t : ℝ) (i : Fin 2) (θ : ℝ) :
    (exp (((-(θ + circularContourAngularVelocities i * t) : ℝ) : ℂ) * I) *
      LittleContourSpace.lift γ
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
          (contourParameterShiftFamilyCLM γ (fun j => circularContourAngularVelocities j * t)
            (circularNormalModeLittle hγ hγ1.le N η τ)) i) θ).re / circularContourRadii i +
      circularContourAngularVelocities i *
        (τ i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) (θ + circularContourAngularVelocities i * t)).re +
      (N + 2 : ℕ) * circularContourAngularVelocities i *
        (η i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) (θ + circularContourAngularVelocities i * t)).im =
      (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec
        (fun j => η j * contourCircleCharacter ((N + 2 : ℕ) : ℤ)
          (θ + circularContourAngularVelocities i * t))) i).re := by
  rw [fderiv_circularBanachField_material_orbit]
  simp only [contourParameterShiftFamilyCLM_apply, lift_contourParameterShiftLittleCLM]
  exact circularNormalFourierIdentity_banachField hγ hγ1 N η τ i
    (θ + circularContourAngularVelocities i * t)

end Euler2D

end
