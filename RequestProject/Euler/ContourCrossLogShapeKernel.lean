module

public import RequestProject.Euler.ContourCrossLogHolder
public import RequestProject.Euler.ContourLogDerivativeShapeLipschitz

/-! # Genuine Hölder-norm differences of the separated cross kernel -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

open HolderFunctionSpace

def contourCrossDenominatorFactor (γ : ℝ) : ℝ := contourValueHolderConstant γ + 1

theorem contourCrossDenominatorFactor_one_le (γ : ℝ) : 1 ≤ contourCrossDenominatorFactor γ := by
  unfold contourCrossDenominatorFactor
  linarith [contourValueHolderConstant_pos γ]

theorem norm_contourCrossDenominatorHolder_le_uniform {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {M : ℝ} (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (φ : ℝ) :
    ‖contourCrossDenominatorHolder hγ1 Z W φ‖ ≤ contourCrossDenominatorFactor (γ : ℝ) * M := by
  apply (norm_contourCrossDenominatorHolder_le hγ1 Z W φ).trans
  calc
    _ ≤ contourValueHolderConstant (γ : ℝ) * M + M := add_le_add
      (mul_le_mul_of_nonneg_left hZM (contourValueHolderConstant_pos _).le) hWM
    _ = _ := by unfold contourCrossDenominatorFactor; ring

theorem norm_contourCrossDenominatorHolder_shape_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W Z' W' : ContourC1Space γ) (φ : ℝ) :
    ‖contourCrossDenominatorHolder hγ1 Z W φ - contourCrossDenominatorHolder hγ1 Z' W' φ‖ ≤
      contourValueHolderConstant (γ : ℝ) * ‖Z - Z'‖ + ‖W - W'‖ := by
  have he : contourCrossDenominatorHolder hγ1 Z W φ - contourCrossDenominatorHolder hγ1 Z' W' φ =
      (contourC1ValueHolder hγ1 Z - contourC1ValueHolder hγ1 Z') -
        contourHolderConstantCLM γ (ContourC1Space.lift γ W φ - ContourC1Space.lift γ W' φ) := by
    apply HolderFunctionSpace.ext
    intro x
    change (ContourC1Space.toBCF γ Z x - ContourC1Space.lift γ W φ) -
      (ContourC1Space.toBCF γ Z' x - ContourC1Space.lift γ W' φ) =
      (ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ Z' x) -
        (ContourC1Space.lift γ W φ - ContourC1Space.lift γ W' φ)
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_contourC1ValueHolder_sub_le hγ1 Z Z')
  apply (norm_const_le γ _).trans
  exact ContourC1Space.norm_eval_le (W - W') (φ : ContourCircle)

def contourCrossQuotientShapeConstant (γ σ M : ℝ) : ℝ :=
  contourCauchyShapeParameterConstant σ (contourCrossDenominatorFactor γ * M) *
    contourCrossDenominatorFactor γ

theorem contourCrossQuotientShapeConstant_nonneg {γ σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) :
    0 ≤ contourCrossQuotientShapeConstant γ σ M := by
  have hT : 0 ≤ contourCrossDenominatorFactor γ := zero_le_one.trans (contourCrossDenominatorFactor_one_le _)
  exact mul_nonneg (contourCauchyShapeParameterConstant_nonneg hσ (mul_nonneg hT hM)) hT

theorem norm_contourCrossQuotientHolder_le_uniform {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (φ : ℝ) :
    ‖contourCrossQuotientHolder hγ1 Z W hσ hsep φ‖ ≤
      2 * M * inverseBound σ (contourCrossDenominatorFactor (γ : ℝ) * M) := by
  have hi := norm_inverseOfNormLower_le_uniform (contourCrossDenominatorHolder hγ1 Z W φ) hσ
    (norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep φ)
    (norm_contourCrossDenominatorHolder_le_uniform hγ1 Z W hZM hWM φ)
  have hB := (inverseBound_pos hσ (contourCrossDenominatorFactor (γ : ℝ) * M)).le
  apply (norm_pointwiseMul_le _ _).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left ((ContourC1Space.norm_derivative_le Z).trans hZM) (by norm_num))
    hi (norm_nonneg _) (by positivity)

theorem norm_contourCrossQuotientHolder_shape_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hZ'M : ‖Z'‖ ≤ M) (hW'M : ‖W'‖ ≤ M) (φ : ℝ) :
    ‖contourCrossQuotientHolder hγ1 Z W hσ hsep φ - contourCrossQuotientHolder hγ1 Z' W' hσ hsep' φ‖ ≤
      contourCrossQuotientShapeConstant (γ : ℝ) σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
  let T := contourCrossDenominatorFactor (γ : ℝ)
  let δ := ‖Z - Z'‖ + ‖W - W'‖
  have hT : 1 ≤ T := contourCrossDenominatorFactor_one_le _
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hδZ : ‖Z - Z'‖ ≤ T * δ :=
    (le_add_of_nonneg_right (norm_nonneg (W - W'))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT hδ)
  have hden : ‖contourCrossDenominatorHolder hγ1 Z W φ - contourCrossDenominatorHolder hγ1 Z' W' φ‖ ≤ T * δ := by
    apply (norm_contourCrossDenominatorHolder_shape_sub_le hγ1 Z W Z' W' φ).trans
    dsimp only [T, δ, contourCrossDenominatorFactor]
    have hD := (contourValueHolderConstant_pos (γ : ℝ)).le
    nlinarith [norm_nonneg (Z - Z'), mul_nonneg hD (norm_nonneg (W - W'))]
  have hMle : M ≤ T * M := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT hM
  have hnum : ‖ContourC1Space.derivative γ Z - ContourC1Space.derivative γ Z'‖ ≤ T * δ := by
    rw [← map_sub]
    exact (ContourC1Space.norm_derivative_le (Z - Z')).trans hδZ
  have hq := norm_divideOfNormLower_sub_le_uniform
    (ContourC1Space.derivative γ Z) (ContourC1Space.derivative γ Z')
    (contourCrossDenominatorHolder hγ1 Z W φ) (contourCrossDenominatorHolder hγ1 Z' W' φ)
    hσ (mul_nonneg hT0 hM) (norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep φ)
    (norm_contourCrossDenominatorHolder_lower hγ1 Z' W' hsep' φ)
    (((ContourC1Space.norm_derivative_le Z').trans hZ'M).trans hMle)
    (norm_contourCrossDenominatorHolder_le_uniform hγ1 Z W hZM hWM φ)
    (norm_contourCrossDenominatorHolder_le_uniform hγ1 Z' W' hZ'M hW'M φ) hnum hden
  apply hq.trans_eq
  unfold contourCrossQuotientShapeConstant
  dsimp only [T, δ]
  ring

def contourCrossDerivativeKernelShapeConstant (γ σ M : ℝ) : ℝ :=
  2 * M * contourCrossQuotientShapeConstant γ σ M +
    4 * M * inverseBound σ (contourCrossDenominatorFactor γ * M)

theorem contourCrossDerivativeKernelShapeConstant_nonneg {γ σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) :
    0 ≤ contourCrossDerivativeKernelShapeConstant γ σ M := by
  have hQ := contourCrossQuotientShapeConstant_nonneg (γ := γ) hσ hM
  have hB := (inverseBound_pos hσ (contourCrossDenominatorFactor γ * M)).le
  unfold contourCrossDerivativeKernelShapeConstant
  positivity

theorem norm_contourCrossDerivativeKernelHolder_shape_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hZ'M : ‖Z'‖ ≤ M) (hW'M : ‖W'‖ ≤ M) (φ : ℝ) :
    ‖contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep φ -
      contourCrossDerivativeKernelHolder hγ1 Z' W' hσ hsep' φ‖ ≤
      contourCrossDerivativeKernelShapeConstant (γ : ℝ) σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
  let q := contourCrossQuotientHolder hγ1 Z W hσ hsep φ
  let q' := contourCrossQuotientHolder hγ1 Z' W' hσ hsep' φ
  let d := contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W) φ)
  let d' := contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W') φ)
  let δ := ‖Z - Z'‖ + ‖W - W'‖
  let B := inverseBound σ (contourCrossDenominatorFactor (γ : ℝ) * M)
  have hB : 0 ≤ B := (inverseBound_pos hσ _).le
  have hQ := contourCrossQuotientShapeConstant_nonneg (γ := (γ : ℝ)) hσ hM
  have hd : ‖d‖ ≤ M := (norm_const_le γ _).trans ((ContourC1Space.norm_deriv_lift_le W φ).trans hWM)
  have hdd : ‖d - d'‖ ≤ δ := by
    apply le_trans _ (le_add_of_nonneg_left (norm_nonneg (Z - Z')))
    change ‖contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W) φ) -
      contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W') φ)‖ ≤ ‖W - W'‖
    rw [← map_sub]
    apply (norm_const_le γ _).trans
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
    exact ContourC1Space.norm_derivativeEval_le (W - W') (φ : ContourCircle)
  have hqp : ‖contourHolderRealPart q'‖ ≤ 2 * M * B :=
    (norm_contourHolderRealPart_le _).trans (norm_contourCrossQuotientHolder_le_uniform hγ1 Z' W' hσ hsep' hM hZ'M hW'M φ)
  have hqd : ‖contourHolderRealPart q - contourHolderRealPart q'‖ ≤
      contourCrossQuotientShapeConstant (γ : ℝ) σ M * δ := by
    change ‖contourHolderRealPartCLM γ q - contourHolderRealPartCLM γ q'‖ ≤ _
    rw [← map_sub]
    exact (norm_contourHolderRealPart_le _).trans
      (norm_contourCrossQuotientHolder_shape_sub_le hγ1 Z W Z' W' hσ hsep hsep' hM hZM hWM hZ'M hW'M φ)
  apply (norm_contourHolder_pointwiseMul_sub_le (contourHolderRealPart q) (contourHolderRealPart q') d d').trans
  calc
    _ ≤ 2 * (contourCrossQuotientShapeConstant (γ : ℝ) σ M * δ) * M + 2 * (2 * M * B) * δ :=
      add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hqd (by norm_num)) hd (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left hqp (by norm_num)) hdd (norm_nonneg _) (by positivity))
    _ = _ := by unfold contourCrossDerivativeKernelShapeConstant; dsimp only [B, δ]; ring

end Euler2D

end
