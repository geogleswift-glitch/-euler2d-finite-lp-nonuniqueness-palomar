module

public import RequestProject.Euler.CircularNormalMatrix
public import RequestProject.Euler.ContourCircularRotationDerivative

/-! The actual normal Fourier identity at every angular parameter.
It is an identity for the derivative of the original Banach field;
the integration of the full-period variational equation is separate. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) normalFourierC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) normalFourierC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) normalFourierLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) normalFourierLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 800000 in
theorem circularNormalFourierIdentity_C1 {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) (θ : ℝ) :
    (exp (((-θ : ℝ) : ℂ) * I) *
      contourC1BoundaryDerivative circularContourStrengths
        (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i θ
          (circularNormalModeC1 hγ hγ1 N η τ)).re / circularContourRadii i +
      circularContourAngularVelocities i * (τ i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).re +
      (N + 2 : ℕ) * circularContourAngularVelocities i * (η i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).im =
      (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec
        (fun j => η j * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ)) i).re := by
  let ηθ : Fin 2 → ℂ := fun j => η j * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ
  let τθ : Fin 2 → ℂ := fun j => τ j * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ
  have hr (j : Fin 2) : 0 < circularContourRadii j := by
    fin_cases j <;> simp [circularContourRadii, cellA_pos]
  have hinj : Function.Injective circularContourRadii := by
    intro j k h
    fin_cases j <;> fin_cases k <;>
      simp_all [circularContourRadii, cellA_lt_one.ne, cellA_lt_one.ne.symm]
  have hrotate : contourRotationFamilyC1CLM γ (-θ) (circularNormalModeC1 hγ hγ1 N η τ) =
      circularNormalModeC1 hγ hγ1 N ηθ τθ := by
    funext j
    change contourRotationC1 (-θ) (circularNormalModeC1 hγ hγ1 N η τ j) = _
    have h := contourRotationC1_normal_mode hγ hγ1 N η τ (-θ) j
    simpa only [contourCircleCharacter_neg_arg, neg_neg] using h
  have hcov := circularBoundaryDerivative_rotation hγ hγ1 circularContourRadii hr hinj
    circularContourStrengths (circularNormalModeC1 hγ hγ1 N η τ) (-θ) i 0
  rw [hrotate] at hcov
  simp only [sub_neg_eq_add, zero_add] at hcov
  have h0 := circularNormalMatrix_C1_zero hγ hγ1 N ηθ τθ i
  rw [hcov] at h0
  exact h0

set_option maxHeartbeats 800000 in
theorem circularNormalFourierIdentity_banachField {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) (θ : ℝ) :
    (exp (((-θ : ℝ) : ℂ) * I) * LittleContourSpace.lift γ
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
          (circularNormalModeLittle hγ hγ1.le N η τ) i) θ).re / circularContourRadii i +
      circularContourAngularVelocities i * (τ i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).re +
      (N + 2 : ℕ) * circularContourAngularVelocities i * (η i * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ).im =
      (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec
        (fun j => η j * contourCircleCharacter ((N + 2 : ℕ) : ℤ) θ)) i).re := by
  let Z : AdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii :=
    ⟨littleCircularReference hγ hγ1, admissible_littleCircularReference hγ hγ1⟩
  let hr : ∀ i : Fin 2, 0 < circularContourRadii i :=
    fun i => by fin_cases i <;> simp [circularContourRadii, cellA_pos]
  let H := circularNormalModeLittle hγ hγ1.le N η τ
  have hfield : fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H =
      fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1)
        circularContourRadii hr (lift_circularReferenceC1 hγ hγ1) circularContourStrengths)
          (littleCircularReference hγ hγ1) H := by
    have h := fderiv_finiteContourPhaseFieldTotal_conjugate hγ hγ1
      (circularReferenceC1 hγ hγ1) circularContourRadii hr
      (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z 0 H
    simpa only [contourParameterShiftFamilyCLM_zero] using h
  have hread := lift_fderiv_finiteContourMaterialFieldTotal hγ hγ1
    (circularReferenceC1 hγ hγ1) circularContourRadii hr
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z H i θ
  have he : LittleContourSpace.lift γ
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H i) θ =
      contourC1BoundaryDerivative circularContourStrengths
        (fun j => circularReferenceContourC1 hγ hγ1.le (circularContourRadii j)) i θ
          (circularNormalModeC1 hγ hγ1.le N η τ) := by
    rw [hfield]
    exact hread
  rw [he]
  exact circularNormalFourierIdentity_C1 hγ hγ1.le N η τ i θ

end Euler2D

end
