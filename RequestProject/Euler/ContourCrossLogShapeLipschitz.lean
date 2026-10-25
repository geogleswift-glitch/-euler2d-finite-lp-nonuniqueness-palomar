module

public import RequestProject.Euler.ContourCrossLogShapeKernel
public import RequestProject.Euler.ContourCrossLogC1
public import RequestProject.Euler.ContourLogShapeBounds

/-! # Actual C¹ Hölder shape bounds for the separated cross-interaction -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

def contourCrossLogDerivativeShapeConstant (γ σ M : ℝ) : ℝ :=
  (2 * Real.pi) * contourCrossDerivativeKernelShapeConstant γ σ M

theorem norm_contourCrossLogDerivativeHolder_shape_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hZ'M : ‖Z'‖ ≤ M) (hW'M : ‖W'‖ ≤ M) :
    ‖contourCrossLogDerivativeHolder hγ1 Z W hσ hsep - contourCrossLogDerivativeHolder hγ1 Z' W' hσ hsep'‖ ≤
      contourCrossLogDerivativeShapeConstant (γ : ℝ) σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
  unfold contourCrossLogDerivativeHolder
  rw [← integral_sub (integrableOn_contourCrossDerivativeKernelHolder hγ1 Z W hσ hsep)
    (integrableOn_contourCrossDerivativeKernelHolder hγ1 Z' W' hσ hsep')]
  calc
    _ ≤ ∫ φ in Icc (-Real.pi) Real.pi,
        contourCrossDerivativeKernelShapeConstant (γ : ℝ) σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
      apply norm_integral_le_of_norm_le (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [] with φ
      exact norm_contourCrossDerivativeKernelHolder_shape_sub_le hγ1 Z W Z' W' hσ hsep hsep'
        hM hZM hWM hZ'M hW'M φ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), intervalIntegral.integral_const]
      unfold contourCrossLogDerivativeShapeConstant
      simp only [smul_eq_mul]
      ring

theorem abs_contourCrossLogKernel_le {γ : ℝ≥0} (Z W : ContourC1Space γ) {σ M : ℝ}
    (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (θ φ : ℝ) :
    |Real.log ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖| ≤
      |Real.log σ| + |Real.log (2 * M + 1)| := by
  have hupper : ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ ≤ 2 * M + 1 := by
    have hz : ‖ContourC1Space.lift γ Z θ‖ ≤ M := (ContourC1Space.norm_eval_le Z (θ : ContourCircle)).trans hZM
    have hw : ‖ContourC1Space.lift γ W φ‖ ≤ M := (ContourC1Space.norm_eval_le W (φ : ContourCircle)).trans hWM
    linarith [norm_sub_le (ContourC1Space.lift γ Z θ) (ContourC1Space.lift γ W φ)]
  have hlower := hsep (θ : ContourCircle) (φ : ContourCircle)
  change σ ≤ ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ at hlower
  simpa only [mul_one, Real.log_one, abs_zero, add_zero] using
    abs_log_le_of_mul_lower hσ (by norm_num : (0 : ℝ) < 1)
      (by simpa only [mul_one] using hlower) hupper

theorem norm_contourCrossLogIntegrand_shape_sub_le {γ : ℝ≥0}
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hW'M : ‖W'‖ ≤ M) (θ φ : ℝ) :
    ‖contourCrossLogIntegrand (ContourC1Space.lift γ Z) (ContourC1Space.lift γ W)
        (deriv (ContourC1Space.lift γ W)) θ φ -
      contourCrossLogIntegrand (ContourC1Space.lift γ Z') (ContourC1Space.lift γ W')
        (deriv (ContourC1Space.lift γ W')) θ φ‖ ≤
      (|Real.log σ| + |Real.log (2 * M + 1)| + M / σ) * (‖Z - Z'‖ + ‖W - W'‖) := by
  let a := ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ
  let b := ContourC1Space.lift γ Z' θ - ContourC1Space.lift γ W' φ
  let δ := ‖Z - Z'‖ + ‖W - W'‖
  have hd : ‖a - b‖ ≤ δ := by
    have he : a - b = (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z' θ) -
        (ContourC1Space.lift γ W φ - ContourC1Space.lift γ W' φ) := by dsimp only [a, b]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add
      (ContourC1Space.norm_eval_le (Z - Z') (θ : ContourCircle))
      (ContourC1Space.norm_eval_le (W - W') (φ : ContourCircle)))
  have hl : |Real.log ‖a‖ - Real.log ‖b‖| ≤ δ / σ :=
    (abs_log_sub_log_le_of_lower hσ (hsep (θ : ContourCircle) (φ : ContourCircle))
      (hsep' (θ : ContourCircle) (φ : ContourCircle))).trans
      (div_le_div_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans hd) hσ.le)
  have hla := abs_contourCrossLogKernel_le Z W hσ hsep hZM hWM θ φ
  have hdd : ‖deriv (ContourC1Space.lift γ W) φ - deriv (ContourC1Space.lift γ W') φ‖ ≤ δ := by
    apply le_trans _ (le_add_of_nonneg_left (norm_nonneg (Z - Z')))
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
    exact ContourC1Space.norm_derivativeEval_le (W - W') (φ : ContourCircle)
  have he : contourCrossLogIntegrand (ContourC1Space.lift γ Z) (ContourC1Space.lift γ W)
        (deriv (ContourC1Space.lift γ W)) θ φ -
      contourCrossLogIntegrand (ContourC1Space.lift γ Z') (ContourC1Space.lift γ W')
        (deriv (ContourC1Space.lift γ W')) θ φ =
      Real.log ‖a‖ • (deriv (ContourC1Space.lift γ W) φ - deriv (ContourC1Space.lift γ W') φ) +
        (Real.log ‖a‖ - Real.log ‖b‖) • deriv (ContourC1Space.lift γ W') φ := by
    simp only [contourCrossLogIntegrand, smul_sub, sub_smul, a, b]
    abel
  rw [he]
  calc
    _ ≤ |Real.log ‖a‖| * ‖deriv (ContourC1Space.lift γ W) φ - deriv (ContourC1Space.lift γ W') φ‖ +
        |Real.log ‖a‖ - Real.log ‖b‖| * ‖deriv (ContourC1Space.lift γ W') φ‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (Real.log ‖a‖ • (deriv (ContourC1Space.lift γ W) φ - deriv (ContourC1Space.lift γ W') φ))
        ((Real.log ‖a‖ - Real.log ‖b‖) • deriv (ContourC1Space.lift γ W') φ)
    _ ≤ (|Real.log σ| + |Real.log (2 * M + 1)|) * δ + (δ / σ) * M := add_le_add
      (mul_le_mul hla hdd (norm_nonneg _) (by positivity))
      (mul_le_mul hl ((ContourC1Space.norm_deriv_lift_le W' φ).trans hW'M) (norm_nonneg _)
        (div_nonneg (by dsimp [δ]; positivity) hσ.le))
    _ = _ := by dsimp only [δ]; ring

theorem integrableOn_contourC1CrossLogIntegrand {γ : ℝ≥0} (Z W : ContourC1Space γ) {σ : ℝ}
    (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) (θ : ℝ) :
    IntegrableOn (contourCrossLogIntegrand (ContourC1Space.lift γ Z) (ContourC1Space.lift γ W)
      (deriv (ContourC1Space.lift γ W)) θ) (Icc (-Real.pi) Real.pi) := by
  have hn : ∀ φ : ℝ, ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ ≠ 0 :=
    fun φ => (hσ.trans_le (hsep (θ : ContourCircle) (φ : ContourCircle))).ne'
  have hc : Continuous (fun φ : ℝ => Real.log ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ •
      deriv (ContourC1Space.lift γ W) φ) :=
    ((continuous_const.sub (ContourC1Space.contDiff_lift W).continuous).norm.log hn).smul
      (ContourC1Space.contDiff_lift W).continuous_deriv_one
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

def contourCrossLogValueShapeConstant (σ M : ℝ) : ℝ :=
  (2 * Real.pi) * (|Real.log σ| + |Real.log (2 * M + 1)| + M / σ)

theorem norm_contourC1CrossLogIntegral_shape_sub_le {γ : ℝ≥0}
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hW'M : ‖W'‖ ≤ M) (θ : ℝ) :
    ‖contourC1CrossLogIntegral Z W θ - contourC1CrossLogIntegral Z' W' θ‖ ≤
      contourCrossLogValueShapeConstant σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
  unfold contourC1CrossLogIntegral contourCrossLogIntegral
  rw [← integral_sub (integrableOn_contourC1CrossLogIntegrand Z W hσ hsep θ)
    (integrableOn_contourC1CrossLogIntegrand Z' W' hσ hsep' θ)]
  calc
    _ ≤ ∫ φ in Icc (-Real.pi) Real.pi,
        (|Real.log σ| + |Real.log (2 * M + 1)| + M / σ) * (‖Z - Z'‖ + ‖W - W'‖) := by
      apply norm_integral_le_of_norm_le (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [] with φ
      exact norm_contourCrossLogIntegrand_shape_sub_le Z W Z' W' hσ hsep hsep' hM hZM hWM hW'M θ φ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), intervalIntegral.integral_const]
      unfold contourCrossLogValueShapeConstant
      simp only [smul_eq_mul]
      ring

def contourCrossLogShapeConstant (γ σ M : ℝ) : ℝ :=
  max (contourCrossLogValueShapeConstant σ M) (contourCrossLogDerivativeShapeConstant γ σ M)

theorem contourCrossLogShapeConstant_nonneg {γ σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) :
    0 ≤ contourCrossLogShapeConstant γ σ M := by
  apply le_trans _ (le_max_right _ _)
  exact mul_nonneg (by positivity) (contourCrossDerivativeKernelShapeConstant_nonneg hσ hM)

theorem norm_contourCrossLogC1_shape_sub_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W Z' W' : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z' W' σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (hZ'M : ‖Z'‖ ≤ M) (hW'M : ‖W'‖ ≤ M) :
    ‖contourCrossLogC1 hγ1 Z W hσ hsep - contourCrossLogC1 hγ1 Z' W' hσ hsep'‖ ≤
      contourCrossLogShapeConstant (γ : ℝ) σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
  have hval := norm_contourC1CrossLogIntegral_shape_sub_le Z W Z' W' hσ hsep hsep' hM hZM hWM hW'M
  have hV : 0 ≤ contourCrossLogValueShapeConstant σ M * (‖Z - Z'‖ + ‖W - W'‖) :=
    (norm_nonneg _).trans (hval 0)
  have hF : ‖contourCrossLogBCF hγ1 Z W hσ hsep - contourCrossLogBCF hγ1 Z' W' hσ hsep'‖ ≤
      contourCrossLogValueShapeConstant σ M * (‖Z - Z'‖ + ‖W - W'‖) := by
    apply (BoundedContinuousFunction.norm_le hV).mpr
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact hval θ
  have hG := norm_contourCrossLogDerivativeHolder_shape_sub_le hγ1 Z W Z' W' hσ hsep hsep'
    hM hZM hWM hZ'M hW'M
  change max ‖contourCrossLogBCF hγ1 Z W hσ hsep - contourCrossLogBCF hγ1 Z' W' hσ hsep'‖
      ‖contourCrossLogDerivativeHolder hγ1 Z W hσ hsep - contourCrossLogDerivativeHolder hγ1 Z' W' hσ hsep'‖ ≤ _
  exact max_le (hF.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    (hG.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

theorem contourCrossLogC1_independent_separation {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hsep : ContourCrossSeparated Z W σ) (hsep' : ContourCrossSeparated Z W τ) :
    contourCrossLogC1 hγ1 Z W hσ hsep = contourCrossLogC1 hγ1 Z W hτ hsep' := by
  apply ContourC1Space.ext
  intro x
  rfl

end Euler2D

end
