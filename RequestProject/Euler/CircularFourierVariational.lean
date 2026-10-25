module

public import RequestProject.Euler.CircularFourierModeClosure
public import RequestProject.Euler.ContourFourierModeCalculus

/-! Actual finite Fourier solutions of the original Banach variational
equation. Angular transport and material parametrization are explicit. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) fourierVariationalC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourierVariationalC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) fourierVariationalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourierVariationalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularAngularNormalAmplitude (N : ℕ) (η : Fin 2 → ℂ) : Fin 2 → ℂ :=
  (I • (Bmat (N + 2)).map (fun r : ℝ => (r : ℂ))).mulVec η

def circularAngularTangentialAmplitude (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) : ℂ :=
  circularMaterialTangentialAmplitude N η i - circularContourAngularVelocities i * η i -
    I * (N + 2 : ℕ) * circularContourAngularVelocities i * τ i

theorem circularAngularNormalAmplitude_material (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularAngularNormalAmplitude N η i + I * (N + 2 : ℕ) *
        circularContourAngularVelocities i * η i - circularContourAngularVelocities i * τ i =
      circularMaterialNormalAmplitude N η τ i := by
  fin_cases i <;>
    norm_num [circularAngularNormalAmplitude, circularMaterialNormalAmplitude,
      circularContourAngularVelocities, Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    simp only [← Complex.ofReal_pow] <;> push_cast <;> ring

theorem circularAngularTangentialAmplitude_material (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    circularAngularTangentialAmplitude N η τ i + circularContourAngularVelocities i * η i +
        I * (N + 2 : ℕ) * circularContourAngularVelocities i * τ i =
      circularMaterialTangentialAmplitude N η i := by
  unfold circularAngularTangentialAmplitude
  ring

set_option maxHeartbeats 800000 in
theorem hasDerivAt_shifted_circularNormalModeLittle {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (v : Fin 2 → ℝ)
    {η τ : ℝ → Fin 2 → ℂ} {η' τ' : Fin 2 → ℂ} {t : ℝ}
    (hη : HasDerivAt η η' t) (hτ : HasDerivAt τ τ' t) :
    HasDerivAt (fun s => contourParameterShiftFamilyCLM γ (fun i => v i * s)
        (circularNormalModeLittle hγ hγ1 N (η s) (τ s)))
      (contourParameterShiftFamilyCLM γ (fun i => v i * t)
        (circularNormalModeLittle hγ hγ1 N
          (fun i => η' i + I * (N + 2 : ℕ) * v i * η t i - v i * τ t i)
          (fun i => τ' i + v i * η t i + I * (N + 2 : ℕ) * v i * τ t i))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hηi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hη
  have hτi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hτ
  have hp : HasDerivAt (fun s => circularNormalModePlus (circularContourRadii i) (η s i) (τ s i))
      (circularNormalModePlus (circularContourRadii i) (η' i) (τ' i)) t :=
    (hηi.add (hτi.const_mul I)).const_mul ((circularContourRadii i : ℂ) / 2)
  have hηc : HasDerivAt (fun s => conj (η s i)) (conj (η' i)) t :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hηi
  have hτc : HasDerivAt (fun s => conj (τ s i)) (conj (τ' i)) t :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hτi
  have hm : HasDerivAt (fun s => circularNormalModeMinus (circularContourRadii i) (η s i) (τ s i))
      (circularNormalModeMinus (circularContourRadii i) (η' i) (τ' i)) t :=
    (hηc.add (hτc.const_mul I)).const_mul ((circularContourRadii i : ℂ) / 2)
  have hv : HasDerivAt (fun s : ℝ => v i * s) (v i) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (v i)
  have hplus := hasDerivAt_shifted_littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ) hp hv
  have hminus := hasDerivAt_shifted_littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ)) hm hv
  have hfun : (fun s => contourParameterShiftFamilyCLM γ (fun j => v j * s)
      (circularNormalModeLittle hγ hγ1 N (η s) (τ s)) i) =
      (fun s => contourParameterShiftLittleCLM γ (v i * s)
          (littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ)
            (circularNormalModePlus (circularContourRadii i) (η s i) (τ s i))) +
        contourParameterShiftLittleCLM γ (v i * s)
          (littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ))
            (circularNormalModeMinus (circularContourRadii i) (η s i) (τ s i)))) := by
    funext s
    exact map_add (contourParameterShiftLittleCLM γ (v i * s)) _ _
  rw [hfun]
  convert hplus.add hminus using 1
  rw [← map_add]
  simp only [contourParameterShiftFamilyCLM_apply]
  apply congrArg (contourParameterShiftLittleCLM γ (v i * t))
  unfold circularNormalModeLittle
  apply congrArg₂ (fun a b : LittleContourSpace γ => a + b)
  · congr 1
    apply Complex.ext <;>
      norm_num [circularNormalModePlus, Complex.mul_re, Complex.mul_im] <;> push_cast <;> ring
  · congr 1
    apply Complex.ext <;>
      norm_num [circularNormalModeMinus, Complex.mul_re, Complex.mul_im] <;> push_cast <;> ring

set_option maxHeartbeats 800000 in
theorem hasDerivAt_circularFourier_variational {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (N : ℕ)
    {η τ : ℝ → Fin 2 → ℂ} {t : ℝ}
    (hη : HasDerivAt η (circularAngularNormalAmplitude N (η t)) t)
    (hτ : HasDerivAt τ (circularAngularTangentialAmplitude N (η t) (τ t)) t) :
    HasDerivAt (fun s => contourParameterShiftFamilyCLM γ
        (fun i => circularContourAngularVelocities i * s)
          (circularNormalModeLittle hγ hγ1.le N (η s) (τ s)))
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
        (contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
          (circularNormalModeLittle hγ hγ1.le N (η t) (τ t)))) t := by
  rw [fderiv_circularBanachField_material_orbit, fderiv_circularBanachField_mode]
  have hd := hasDerivAt_shifted_circularNormalModeLittle hγ hγ1.le N
    circularContourAngularVelocities hη hτ
  simpa only [circularAngularNormalAmplitude_material, circularAngularTangentialAmplitude_material] using hd

end Euler2D

end
