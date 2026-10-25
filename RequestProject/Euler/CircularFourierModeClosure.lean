module

public import RequestProject.Euler.CircularOrbitNormalFourier
public import RequestProject.Euler.ContourCircularTangentialResponse

/-! The original field derivative preserves each actual finite Fourier
mode space, including both normal and tangential components. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) modeClosureC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) modeClosureC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) modeClosureLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) modeClosureLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularMaterialNormalAmplitude (N : ℕ) (η τ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![I * (5 / 4 * η 0 - 3 / 4 * (cellA : ℂ) ^ N * η 1) - 1 / 2 * τ 0,
    I * (5 / 4 * (cellA : ℂ) ^ (N + 4) * η 0 - 3 / 4 * η 1)]

def circularMaterialTangentialAmplitude (N : ℕ) (η : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-3 / 4 * η 0 + 3 / 4 * (cellA : ℂ) ^ N * η 1,
    5 / 4 * (cellA : ℂ) ^ (N + 4) * η 0 - 3 / 4 * η 1]

theorem circularMaterialNormalAmplitude_mul (N : ℕ) (η τ : Fin 2 → ℂ) (c : ℂ) :
    circularMaterialNormalAmplitude N (fun i => η i * c) (fun i => τ i * c) =
      fun i => circularMaterialNormalAmplitude N η τ i * c := by
  funext i
  fin_cases i <;> norm_num [circularMaterialNormalAmplitude] <;> ring

theorem circularMaterialTangentialAmplitude_mul (N : ℕ) (η : Fin 2 → ℂ) (c : ℂ) :
    circularMaterialTangentialAmplitude N (fun i => η i * c) =
      fun i => circularMaterialTangentialAmplitude N η i * c := by
  funext i
  fin_cases i <;> norm_num [circularMaterialTangentialAmplitude] <;> ring

set_option maxHeartbeats 800000 in
theorem circularBoundaryDerivative_mode_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    contourC1BoundaryDerivative circularContourStrengths
      (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i 0
        (circularNormalModeC1 hγ hγ1 N η τ) =
      (circularContourRadii i : ℂ) *
        (((circularMaterialNormalAmplitude N η τ i).re : ℂ) +
          I * ((circularMaterialTangentialAmplitude N η i).re : ℂ)) := by
  apply Complex.ext
  · rw [circularBoundaryDerivative_normal_response hγ hγ1 N η τ i]
    fin_cases i <;>
      norm_num [circularMaterialNormalAmplitude, circularContourRadii,
        Complex.mul_re, Complex.mul_im] <;>
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] <;>
      simp only [pow_succ] <;> ring
  · rw [circularBoundaryDerivative_tangential_response hγ hγ1 N η τ i]
    fin_cases i <;>
      norm_num [circularMaterialTangentialAmplitude, circularContourRadii,
        Complex.mul_re, Complex.mul_im] <;>
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] <;>
      simp only [pow_succ] <;> ring

set_option maxHeartbeats 800000 in
theorem circularBoundaryDerivative_mode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) (θ : ℝ) :
    contourC1BoundaryDerivative circularContourStrengths
      (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i θ
        (circularNormalModeC1 hγ hγ1 N η τ) =
      LittleContourSpace.lift γ (circularNormalModeLittle hγ hγ1 N
        (circularMaterialNormalAmplitude N η τ) (circularMaterialTangentialAmplitude N η) i) θ := by
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
    simpa only [contourCircleCharacter_neg_arg, neg_neg] using
      contourRotationC1_normal_mode hγ hγ1 N η τ (-θ) j
  have hcov := circularBoundaryDerivative_rotation hγ hγ1 circularContourRadii hr hinj
    circularContourStrengths (circularNormalModeC1 hγ hγ1 N η τ) (-θ) i 0
  rw [hrotate] at hcov
  simp only [sub_neg_eq_add, zero_add] at hcov
  have he : exp ((θ : ℂ) * I) * exp (((-θ : ℝ) : ℂ) * I) = 1 := by
    rw [← exp_add, show (θ : ℂ) * I + ((-θ : ℝ) : ℂ) * I = 0 by push_cast; ring,
      exp_zero]
  calc
    _ = exp ((θ : ℂ) * I) * (exp (((-θ : ℝ) : ℂ) * I) *
        contourC1BoundaryDerivative circularContourStrengths
          (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i θ
            (circularNormalModeC1 hγ hγ1 N η τ)) := by rw [← mul_assoc, he, one_mul]
    _ = exp ((θ : ℂ) * I) *
        contourC1BoundaryDerivative circularContourStrengths
          (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i 0
            (circularNormalModeC1 hγ hγ1 N ηθ τθ) := by rw [hcov]
    _ = _ := by
      rw [circularBoundaryDerivative_mode_zero, lift_circularNormalModeLittle]
      dsimp only [ηθ, τθ]
      rw [circularMaterialNormalAmplitude_mul, circularMaterialTangentialAmplitude_mul]
      simp only [refCircle]
      ring

set_option maxHeartbeats 800000 in
theorem lift_fderiv_circularBanachField_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) (θ : ℝ) :
    LittleContourSpace.lift γ
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H i) θ =
      contourC1BoundaryDerivative circularContourStrengths
        (fun j => circularReferenceContourC1 hγ hγ1.le (circularContourRadii j)) i θ (fun j => (H j).val) := by
  let Z : AdmissibleLittleContourFamily (circularReferenceC1 hγ hγ1) circularContourRadii :=
    ⟨littleCircularReference hγ hγ1, admissible_littleCircularReference hγ hγ1⟩
  let hr : ∀ i : Fin 2, 0 < circularContourRadii i :=
    fun i => by fin_cases i <;> simp [circularContourRadii, cellA_pos]
  have hfield := fderiv_finiteContourPhaseFieldTotal_conjugate hγ hγ1
    (circularReferenceC1 hγ hγ1) circularContourRadii hr
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z 0 H
  simp only [contourParameterShiftFamilyCLM_zero] at hfield
  rw [show fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1) H =
    fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 (circularReferenceC1 hγ hγ1)
      circularContourRadii hr (lift_circularReferenceC1 hγ hγ1) circularContourStrengths)
        (littleCircularReference hγ hγ1) H from hfield]
  exact lift_fderiv_finiteContourMaterialFieldTotal hγ hγ1
    (circularReferenceC1 hγ hγ1) circularContourRadii hr
    (lift_circularReferenceC1 hγ hγ1) circularContourStrengths Z H i θ

set_option maxHeartbeats 800000 in
theorem fderiv_circularBanachField_mode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ) (η τ : Fin 2 → ℂ) :
    fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
        (circularNormalModeLittle hγ hγ1.le N η τ) =
      circularNormalModeLittle hγ hγ1.le N
        (circularMaterialNormalAmplitude N η τ) (circularMaterialTangentialAmplitude N η) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
    (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγ1.le N η τ) i) θ = _
  rw [lift_fderiv_circularBanachField_reference]
  exact circularBoundaryDerivative_mode hγ hγ1.le N η τ i θ

end Euler2D

end
