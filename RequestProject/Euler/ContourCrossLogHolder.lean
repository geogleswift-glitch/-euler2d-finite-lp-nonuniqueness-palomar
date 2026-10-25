module

public import RequestProject.Euler.ContourCrossLogDifferentiation
public import RequestProject.Euler.ContourHolderValue

/-! # The actual separated cross-log derivative in the genuine Hölder space -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

open HolderFunctionSpace

def ContourCrossSeparated {γ : ℝ≥0} (Z W : ContourC1Space γ) (σ : ℝ) : Prop :=
  ∀ x y : ContourCircle, σ ≤ ‖ContourC1Space.toBCF γ Z x - ContourC1Space.toBCF γ W y‖

def contourCrossDenominatorHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) (φ : ℝ) : ContourHolderSpace γ :=
  contourC1ValueHolder hγ1 Z - contourHolderConstantCLM γ (ContourC1Space.lift γ W φ)

@[simp] theorem contourCrossDenominatorHolder_apply {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) (φ : ℝ) (x : ContourCircle) :
    contourCrossDenominatorHolder hγ1 Z W φ x =
      ContourC1Space.toBCF γ Z x - ContourC1Space.lift γ W φ := rfl

theorem norm_contourCrossDenominatorHolder_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) (φ : ℝ) :
    ‖contourCrossDenominatorHolder hγ1 Z W φ‖ ≤
      contourValueHolderConstant (γ : ℝ) * ‖Z‖ + ‖W‖ := by
  apply (norm_sub_le _ _).trans
  exact add_le_add (norm_contourC1ValueHolder_le hγ1 Z)
    ((HolderFunctionSpace.norm_const_le γ _).trans (ContourC1Space.norm_eval_le W (φ : ContourCircle)))

theorem norm_contourCrossDenominatorHolder_lower {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hsep : ContourCrossSeparated Z W σ) (φ : ℝ)
    (x : ContourCircle) : σ ≤ ‖contourCrossDenominatorHolder hγ1 Z W φ x‖ := hsep x (φ : ContourCircle)

theorem continuous_contourCrossDenominatorHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) : Continuous (contourCrossDenominatorHolder hγ1 Z W) :=
  continuous_const.sub ((contourHolderConstantCLM γ).continuous.comp (ContourC1Space.contDiff_lift W).continuous)

def contourCrossReciprocalHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (φ : ℝ) : ContourHolderSpace γ :=
  inverseOfNormLower (contourCrossDenominatorHolder hγ1 Z W φ) hσ
    (norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep φ)

theorem continuous_contourCrossReciprocalHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    Continuous (contourCrossReciprocalHolder hγ1 Z W hσ hsep) := by
  let N := contourValueHolderConstant (γ : ℝ) * ‖Z‖ + ‖W‖
  let u : ℝ → BoundedNormLowerDomain (X := ContourCircle) γ σ N := fun φ =>
    ⟨contourCrossDenominatorHolder hγ1 Z W φ,
      norm_contourCrossDenominatorHolder_le hγ1 Z W φ,
      norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep φ⟩
  have hu : Continuous u := (continuous_contourCrossDenominatorHolder hγ1 Z W).subtype_mk _
  exact ((continuous_inverseOnBoundedNormLower γ (M := N) hσ).comp hu).congr (fun _ => rfl)

def contourCrossQuotientHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (φ : ℝ) : ContourHolderSpace γ :=
  pointwiseMul (ContourC1Space.derivative γ Z) (contourCrossReciprocalHolder hγ1 Z W hσ hsep φ)

def contourCrossDerivativeKernelHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (φ : ℝ) : ContourHolderSpace γ :=
  pointwiseMul (contourHolderRealPart (contourCrossQuotientHolder hγ1 Z W hσ hsep φ))
    (contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W) φ))

theorem contourCrossDerivativeKernelHolder_coe {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (θ φ : ℝ) :
    contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep φ (θ : ContourCircle) =
      contourCrossLogThetaIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z))
        (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ φ := by
  simp only [contourCrossDerivativeKernelHolder, pointwiseMul_apply, contourHolderRealPart_apply,
    contourCrossQuotientHolder, contourCrossReciprocalHolder, inverseOfNormLower_apply,
    contourCrossDenominatorHolder_apply, contourHolderConstantCLM_apply,
    contourCrossLogThetaIntegrand, ContourC1Space.deriv_lift, ContourC1Space.lift,
    div_eq_mul_inv, Complex.real_smul]

theorem continuous_contourCrossDerivativeKernelHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    Continuous (contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep) := by
  have hq : Continuous (contourCrossQuotientHolder hγ1 Z W hσ hsep) :=
    (pointwiseMulCLM γ (ContourC1Space.derivative γ Z)).continuous.comp
      (continuous_contourCrossReciprocalHolder hγ1 Z W hσ hsep)
  have hr : Continuous (fun φ => contourHolderRealPart (contourCrossQuotientHolder hγ1 Z W hσ hsep φ)) :=
    (contourHolderRealPartCLM γ).continuous.comp hq
  have hd : Continuous (fun φ => contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W) φ)) :=
    (contourHolderConstantCLM γ).continuous.comp (ContourC1Space.contDiff_lift W).continuous_deriv_one
  have hmCL : Continuous (fun p : ContourHolderSpace γ × ContourHolderSpace γ =>
      pointwiseMulCLM (X := ContourCircle) γ p.1 p.2) :=
    (pointwiseMulCLM (X := ContourCircle) γ).isBoundedBilinearMap.continuous
  have hm : Continuous (fun p : ContourHolderSpace γ × ContourHolderSpace γ => pointwiseMul p.1 p.2) :=
    hmCL.congr (fun _ => rfl)
  exact (hm.comp (hr.prodMk hd)).congr (fun _ => rfl)

theorem integrableOn_contourCrossDerivativeKernelHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    IntegrableOn (contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep) (Icc (-Real.pi) Real.pi) :=
  (continuous_contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep).continuousOn.integrableOn_compact isCompact_Icc

def contourCrossLogDerivativeHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    ContourHolderSpace γ :=
  ∫ φ in Icc (-Real.pi) Real.pi, contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep φ

theorem contourCrossLogDerivativeHolder_coe {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) (θ : ℝ) :
    contourCrossLogDerivativeHolder hγ1 Z W hσ hsep (θ : ContourCircle) =
      contourCrossLogDerivativeIntegral (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z))
        (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ := by
  change (HolderFunctionSpace.eval γ (θ : ContourCircle))
      (∫ φ in Icc (-Real.pi) Real.pi, contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep φ) = _
  rw [← (HolderFunctionSpace.eval γ (θ : ContourCircle)).integral_comp_comm
    (integrableOn_contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep)]
  apply integral_congr_ae
  filter_upwards [] with φ
  exact contourCrossDerivativeKernelHolder_coe hγ1 Z W hσ hsep θ φ

def contourCrossLogDerivativeBound (γ σ M : ℝ) : ℝ :=
  (2 * Real.pi) * (4 * M ^ 2 * inverseBound σ ((contourValueHolderConstant γ + 1) * M))

theorem norm_contourCrossDerivativeKernelHolder_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (φ : ℝ) :
    ‖contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep φ‖ ≤
      4 * M ^ 2 * inverseBound σ ((contourValueHolderConstant (γ : ℝ) + 1) * M) := by
  let B := inverseBound σ ((contourValueHolderConstant (γ : ℝ) + 1) * M)
  have hB : 0 ≤ B := (inverseBound_pos hσ _).le
  have hD := (contourValueHolderConstant_pos (γ : ℝ)).le
  have hn : ‖contourCrossDenominatorHolder hγ1 Z W φ‖ ≤
      (contourValueHolderConstant (γ : ℝ) + 1) * M := by
    apply (norm_contourCrossDenominatorHolder_le hγ1 Z W φ).trans
    calc
      _ ≤ contourValueHolderConstant (γ : ℝ) * M + M :=
        add_le_add (mul_le_mul_of_nonneg_left hZM hD) hWM
      _ = _ := by ring
  have hi : ‖contourCrossReciprocalHolder hγ1 Z W hσ hsep φ‖ ≤ B :=
    norm_inverseOfNormLower_le_uniform _ hσ (norm_contourCrossDenominatorHolder_lower hγ1 Z W hsep φ) hn
  have hq : ‖contourCrossQuotientHolder hγ1 Z W hσ hsep φ‖ ≤ 2 * M * B :=
    (norm_pointwiseMul_le _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left ((ContourC1Space.norm_derivative_le Z).trans hZM) (by norm_num))
      hi (norm_nonneg _) (by positivity))
  have hd : ‖contourHolderConstantCLM γ (deriv (ContourC1Space.lift γ W) φ)‖ ≤ M :=
    (HolderFunctionSpace.norm_const_le γ _).trans ((ContourC1Space.norm_deriv_lift_le W φ).trans hWM)
  apply (norm_pointwiseMul_le _ _).trans
  calc
    _ ≤ 2 * (2 * M * B) * M := mul_le_mul
      (mul_le_mul_of_nonneg_left ((norm_contourHolderRealPart_le _).trans hq) (by norm_num))
      hd (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [B]; ring

theorem norm_contourCrossLogDerivativeHolder_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCrossLogDerivativeHolder hγ1 Z W hσ hsep‖ ≤ contourCrossLogDerivativeBound (γ : ℝ) σ M := by
  unfold contourCrossLogDerivativeHolder
  calc
    _ ≤ ∫ φ in Icc (-Real.pi) Real.pi,
        4 * M ^ 2 * inverseBound σ ((contourValueHolderConstant (γ : ℝ) + 1) * M) := by
      apply norm_integral_le_of_norm_le (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [] with φ
      exact norm_contourCrossDerivativeKernelHolder_le hγ1 Z W hσ hsep hM hZM hWM φ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), intervalIntegral.integral_const]
      unfold contourCrossLogDerivativeBound
      simp only [smul_eq_mul]
      ring

end Euler2D

end
