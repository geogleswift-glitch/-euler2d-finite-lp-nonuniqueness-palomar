module

public import RequestProject.Euler.ContourCircularNormalResponse
public import RequestProject.Euler.CircularContourPeriodMap
public import RequestProject.Euler.ContourPhaseFirstVariation

/-! The original circular Banach field gives the stated normal Fourier
matrix at angular parameter zero. Both the moving material frame and
the conversion to Eulerian angle are explicit in the identity. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) normalMatrixC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) normalMatrixC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) normalMatrixLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) normalMatrixLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

set_option maxHeartbeats 600000 in
theorem circularNormalMatrix_C1_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    (contourC1BoundaryDerivative circularContourStrengths
        (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i 0
          (circularNormalModeC1 hγ hγ1 N η τ)).re / circularContourRadii i +
      circularContourAngularVelocities i * (τ i).re +
      (N + 2 : ℕ) * circularContourAngularVelocities i * (η i).im =
      (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec η) i).re := by
  rw [circularBoundaryDerivative_normal_response hγ hγ1 N η τ i]
  fin_cases i
  · norm_num [circularContourRadii, circularContourAngularVelocities, Bmat,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    have ha : cellA ≠ 0 := cellA_pos.ne'
    simp only [pow_succ]
    field_simp [ha]
    <;> ring
  · norm_num [circularContourRadii, circularContourAngularVelocities, Bmat,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    ring

set_option maxHeartbeats 800000 in
theorem circularNormalMatrix_banachField_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    (LittleContourSpace.lift γ
        (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
          (circularNormalModeLittle hγ hγ1.le N η τ) i) 0).re / circularContourRadii i +
      circularContourAngularVelocities i * (τ i).re +
      (N + 2 : ℕ) * circularContourAngularVelocities i * (η i).im =
      (((I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec η) i).re := by
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
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z H i 0
  have he : LittleContourSpace.lift γ
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H i) 0 =
      contourC1BoundaryDerivative circularContourStrengths
        (fun j => circularReferenceContourC1 hγ hγ1.le (circularContourRadii j)) i 0
          (circularNormalModeC1 hγ hγ1.le N η τ) := by
    rw [hfield]
    exact hread
  rw [he]
  exact circularNormalMatrix_C1_zero hγ hγ1.le N η τ i

end Euler2D

end
