module

public import RequestProject.Euler.CircularFourierVariational

/-! A genuine growing solution of the original Banach variational
equation along the circular orbit, with its full tangential component. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) growingVariationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) growingVariationC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) growingVariationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) growingVariationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem lamStar_add_imaginary_ne_zero (c : ℝ) : lamStar + I * (c : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [lamStar, Complex.mul_re] at hr
  exact sigma_pos.ne' hr

def circularGrowingTangent (i : Fin 2) : ℂ :=
  (circularMaterialTangentialAmplitude 2 vPlus i -
      (circularContourAngularVelocities i : ℂ) * vPlus i) /
    (lamStar + I * 4 * (circularContourAngularVelocities i : ℂ))

theorem circularGrowingTangent_equation :
    circularAngularTangentialAmplitude 2 vPlus circularGrowingTangent =
      lamStar • circularGrowingTangent := by
  funext i
  have hn : lamStar + I * 4 * (circularContourAngularVelocities i : ℂ) ≠ 0 := by
    convert lamStar_add_imaginary_ne_zero (4 * circularContourAngularVelocities i) using 1 <;>
      push_cast <;> ring
  have he : (lamStar + I * 4 * (circularContourAngularVelocities i : ℂ)) *
      circularGrowingTangent i = circularMaterialTangentialAmplitude 2 vPlus i -
        (circularContourAngularVelocities i : ℂ) * vPlus i := by
    unfold circularGrowingTangent
    exact mul_div_cancel₀ _ hn
  change circularMaterialTangentialAmplitude 2 vPlus i -
      (circularContourAngularVelocities i : ℂ) * vPlus i -
      I * (2 + 2 : ℕ) * (circularContourAngularVelocities i : ℂ) * circularGrowingTangent i =
    lamStar * circularGrowingTangent i
  rw [← he]
  norm_num
  ring

theorem circularAngularNormalAmplitude_smul (N : ℕ) (c : ℂ) (η : Fin 2 → ℂ) :
    circularAngularNormalAmplitude N (c • η) = c • circularAngularNormalAmplitude N η :=
  Matrix.mulVec_smul _ _ _

theorem circularAngularTangentialAmplitude_smul (N : ℕ) (c : ℂ) (η τ : Fin 2 → ℂ) :
    circularAngularTangentialAmplitude N (c • η) (c • τ) =
      c • circularAngularTangentialAmplitude N η τ := by
  have hη : c • η = (fun j => η j * c) := by
    funext j
    exact mul_comm _ _
  have hm (i : Fin 2) : circularMaterialTangentialAmplitude N (c • η) i =
      c * circularMaterialTangentialAmplitude N η i := by
    rw [hη, circularMaterialTangentialAmplitude_mul]
    exact mul_comm _ _
  funext i
  simp only [circularAngularTangentialAmplitude, Pi.smul_apply, smul_eq_mul, hm]
  ring

def circularGrowingNormal (t : ℝ) : Fin 2 → ℂ := exp ((t : ℂ) * lamStar) • vPlus
def circularGrowingTangential (t : ℝ) : Fin 2 → ℂ := exp ((t : ℂ) * lamStar) • circularGrowingTangent

theorem hasDerivAt_circularGrowingScalar (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((s : ℂ) * lamStar))
      (lamStar * exp ((t : ℂ) * lamStar)) t := by
  convert (((hasDerivAt_id t).ofReal_comp).mul_const lamStar).cexp using 1 <;>
    simp only [id_eq, Complex.ofReal_one, one_mul] <;> ring

theorem circularGrowingNormal_hasDerivAt (t : ℝ) :
    HasDerivAt circularGrowingNormal (circularAngularNormalAmplitude 2 (circularGrowingNormal t)) t := by
  have he : circularAngularNormalAmplitude 2 (circularGrowingNormal t) =
      lamStar • circularGrowingNormal t := by
    change (I • (Bmat 4).map (fun r : ℝ => (r : ℂ))).mulVec
        (exp ((t : ℂ) * lamStar) • vPlus) =
      lamStar • (exp ((t : ℂ) * lamStar) • vPlus)
    rw [Matrix.mulVec_smul, iB4_vPlus, smul_smul, smul_smul, mul_comm]
  rw [he]
  simpa only [circularGrowingNormal, smul_smul] using
    (hasDerivAt_circularGrowingScalar t).smul_const vPlus

theorem circularGrowingTangential_hasDerivAt (t : ℝ) :
    HasDerivAt circularGrowingTangential
      (circularAngularTangentialAmplitude 2 (circularGrowingNormal t) (circularGrowingTangential t)) t := by
  have he : circularAngularTangentialAmplitude 2 (circularGrowingNormal t) (circularGrowingTangential t) =
      lamStar • circularGrowingTangential t := by
    rw [circularGrowingNormal, circularGrowingTangential,
      circularAngularTangentialAmplitude_smul, circularGrowingTangent_equation,
      smul_smul, smul_smul, mul_comm]
  rw [he]
  simpa only [circularGrowingTangential, smul_smul] using
    (hasDerivAt_circularGrowingScalar t).smul_const circularGrowingTangent

def circularGrowingVariation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (t : ℝ) : Fin 2 → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
    (circularNormalModeLittle hγ hγ1.le 2 (circularGrowingNormal t) (circularGrowingTangential t))

theorem circularGrowingVariation_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    HasDerivAt (circularGrowingVariation hγ hγ1)
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
        (circularGrowingVariation hγ hγ1 t)) t :=
  hasDerivAt_circularFourier_variational hγ hγ1 2
    (circularGrowingNormal_hasDerivAt t) (circularGrowingTangential_hasDerivAt t)

theorem circularGrowingVariation_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularGrowingVariation hγ hγ1 0 =
      circularNormalModeLittle hγ hγ1.le 2 vPlus circularGrowingTangent := by
  simp only [circularGrowingVariation, circularGrowingNormal, circularGrowingTangential,
    Complex.ofReal_zero, zero_mul, exp_zero, one_smul, mul_zero]
  exact contourParameterShiftFamilyCLM_zero _

theorem contourParameterShiftFamily_circular_period {γ : ℝ≥0}
    (H : Fin 2 → LittleContourSpace γ) :
    contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * period) H = H := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (circularContourAngularVelocities i * period) (H i)) θ =
    LittleContourSpace.lift γ (H i) θ
  rw [lift_contourParameterShiftLittleCLM]
  fin_cases i
  · change LittleContourSpace.lift γ (H 0) (θ + (1 / 2 : ℝ) * period) =
      LittleContourSpace.lift γ (H 0) θ
    have he : (1 / 2 : ℝ) * period = 2 * Real.pi := by unfold period; ring
    rw [he]
    exact LittleContourSpace.periodic_lift (H 0) θ
  · change LittleContourSpace.lift γ (H 1) (θ + 0 * period) = LittleContourSpace.lift γ (H 1) θ
    simp only [zero_mul, add_zero]

theorem circularNormalModeLittle_real_smul {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (c : ℝ) (η τ : Fin 2 → ℂ) :
    circularNormalModeLittle hγ hγ1 N (c • η) (c • τ) =
      c • circularNormalModeLittle hγ hγ1 N η τ := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (circularNormalModeLittle hγ hγ1 N (c • η) (c • τ) i) θ =
    c • LittleContourSpace.lift γ (circularNormalModeLittle hγ hγ1 N η τ i) θ
  rw [lift_circularNormalModeLittle, lift_circularNormalModeLittle]
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero]
  push_cast
  ring

theorem circularGrowingVariation_period {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularGrowingVariation hγ hγ1 period =
      (-lamMult : ℝ) • circularGrowingVariation hγ hγ1 0 := by
  rw [circularGrowingVariation, contourParameterShiftFamily_circular_period,
    circularGrowingNormal, circularGrowingTangential, period_multipliers_m4.1,
    circularGrowingVariation_zero]
  have he (v : Fin 2 → ℂ) : (-(lamMult : ℂ)) • v = (-lamMult : ℝ) • v := by
    funext i
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_neg, smul_eq_mul]
  rw [he, he, circularNormalModeLittle_real_smul]

theorem circularGrowingVariation_ne_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) : circularGrowingVariation hγ hγ1 0 ≠ 0 := by
  intro hzero
  have he := congrArg (fun H : Fin 2 → LittleContourSpace γ =>
    (LittleContourSpace.lift γ (H 0) 0).re) hzero
  rw [circularGrowingVariation_zero] at he
  dsimp only at he
  rw [lift_circularNormalModeLittle] at he
  norm_num [vPlus, contourCircleCharacter_at_zero, refCircle, circularContourRadii,
    Complex.mul_re, Complex.mul_im] at he
  exact cellA_pos.ne' he

theorem norm_circularGrowingVariation_period_gt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ‖circularGrowingVariation hγ hγ1 0‖ < ‖circularGrowingVariation hγ hγ1 period‖ := by
  rw [circularGrowingVariation_period, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (lt_trans zero_lt_one one_lt_lamMult)]
  simpa only [one_mul] using mul_lt_mul_of_pos_right one_lt_lamMult
    (norm_pos_iff.mpr (circularGrowingVariation_ne_zero hγ hγ1))

end Euler2D

end
