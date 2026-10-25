module

public import RequestProject.Euler.ContourCircularFieldModes

/-! Strong Banach derivatives of actual finite Fourier perturbations.
The coefficient maps take values in the original little contour space. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) modeCalculusC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) modeCalculusC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) modeCalculusLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) modeCalculusLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def littleContourFourierModeCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) :
    ℂ →L[ℝ] LittleContourSpace γ :=
  Complex.reCLM.smulRight (littleContourFourierMode hγ hγ1 n 1) +
    Complex.imCLM.smulRight (littleContourFourierMode hγ hγ1 n I)

@[simp] theorem littleContourFourierModeCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) (a : ℂ) :
    littleContourFourierModeCLM hγ hγ1 n a = littleContourFourierMode hγ hγ1 n a := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (a.re : ℝ) • (1 * contourCircleCharacter n θ) +
    (a.im : ℝ) • (I * contourCircleCharacter n θ) = a * contourCircleCharacter n θ
  simp only [Complex.real_smul, one_mul]
  calc
    _ = ((a.re : ℂ) + a.im * I) * contourCircleCharacter n θ := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem hasDerivAt_littleContourFourierMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ)
    {a : ℝ → ℂ} {a' : ℂ} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => littleContourFourierMode hγ hγ1 n (a s))
      (littleContourFourierMode hγ hγ1 n a') t := by
  simpa only [Function.comp_def, littleContourFourierModeCLM_apply] using
    (littleContourFourierModeCLM hγ hγ1 n).hasFDerivAt.comp_hasDerivAt t ha

theorem hasDerivAt_circularNormalModeLittle {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ)
    {η τ : ℝ → Fin 2 → ℂ} {η' τ' : Fin 2 → ℂ} {t : ℝ}
    (hη : HasDerivAt η η' t) (hτ : HasDerivAt τ τ' t) :
    HasDerivAt (fun s => circularNormalModeLittle hγ hγ1 N (η s) (τ s))
      (circularNormalModeLittle hγ hγ1 N η' τ') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hηi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hη
  have hτi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hτ
  have hp : HasDerivAt (fun s => circularNormalModePlus (circularContourRadii i) (η s i) (τ s i))
      (circularNormalModePlus (circularContourRadii i) (η' i) (τ' i)) t := by
    exact (hηi.add (hτi.const_mul I)).const_mul ((circularContourRadii i : ℂ) / 2)
  have hηc : HasDerivAt (fun s => conj (η s i)) (conj (η' i)) t :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hηi
  have hτc : HasDerivAt (fun s => conj (τ s i)) (conj (τ' i)) t :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hτi
  have hm : HasDerivAt (fun s => circularNormalModeMinus (circularContourRadii i) (η s i) (τ s i))
      (circularNormalModeMinus (circularContourRadii i) (η' i) (τ' i)) t := by
    exact (hηc.add (hτc.const_mul I)).const_mul ((circularContourRadii i : ℂ) / 2)
  exact (hasDerivAt_littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ) hp).add
    (hasDerivAt_littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ)) hm)

theorem contourParameterShiftLittleCLM_fourier {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ) (a : ℂ) (b : ℝ) :
    contourParameterShiftLittleCLM γ b (littleContourFourierMode hγ hγ1 n a) =
      littleContourFourierMode hγ hγ1 n (a * contourCircleCharacter n b) := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ b (littleContourFourierMode hγ hγ1 n a)) θ =
    (a * contourCircleCharacter n b) * contourCircleCharacter n θ
  rw [lift_contourParameterShiftLittleCLM, lift_littleContourFourierMode,
    contourCircleCharacter_add_arg]
  ring

theorem hasDerivAt_contourCircleCharacter_comp (n : ℤ)
    {b : ℝ → ℝ} {b' t : ℝ} (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => contourCircleCharacter n (b s))
      ((n : ℂ) * I * (b' : ℂ) * contourCircleCharacter n (b t)) t := by
  convert (hasDerivAt_contourCircleCharacter n (b t)).scomp t hb using 1
  · rfl
  · simp only [Complex.real_smul]
    ring

theorem hasDerivAt_shifted_littleContourFourierMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℤ)
    {a : ℝ → ℂ} {a' : ℂ} {b : ℝ → ℝ} {b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => contourParameterShiftLittleCLM γ (b s)
        (littleContourFourierMode hγ hγ1 n (a s)))
      (contourParameterShiftLittleCLM γ (b t)
        (littleContourFourierMode hγ hγ1 n (a' + (n : ℂ) * I * (b' : ℂ) * a t))) t := by
  simp_rw [contourParameterShiftLittleCLM_fourier]
  have hprod := ha.mul (hasDerivAt_contourCircleCharacter_comp n hb)
  have hd := hasDerivAt_littleContourFourierMode hγ hγ1 n hprod
  convert hd using 1
  congr 1
  ring

end Euler2D

end
