module

public import RequestProject.Euler.ContourCrossLogHolder
public import RequestProject.Euler.ContourLogKernel

/-! # The literal separated cross-interaction as an actual C¹ Hölder contour -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

def contourC1CrossLogIntegral {γ : ℝ≥0} (Z W : ContourC1Space γ) : ℝ → ℂ :=
  contourCrossLogIntegral (ContourC1Space.lift γ Z) (ContourC1Space.lift γ W)
    (deriv (ContourC1Space.lift γ W))

theorem hasDerivAt_contourC1CrossLogIntegral {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) (θ : ℝ) :
    HasDerivAt (contourC1CrossLogIntegral Z W)
      (contourCrossLogDerivativeHolder hγ1 Z W hσ hsep (θ : ContourCircle)) θ := by
  rw [contourCrossLogDerivativeHolder_coe]
  exact hasDerivAt_contourCrossLogIntegral (ContourC1Space.contDiff_lift Z).continuous
    (ContourC1Space.contDiff_lift Z).continuous_deriv_one (ContourC1Space.contDiff_lift W).continuous
    (ContourC1Space.contDiff_lift W).continuous_deriv_one hσ
    (fun t => (ContourC1Space.hasDerivAt_lift Z t).differentiableAt.hasDerivAt)
    (fun θ φ _ => hsep (θ : ContourCircle) (φ : ContourCircle)) θ

theorem periodic_contourC1CrossLogIntegral {γ : ℝ≥0} (Z W : ContourC1Space γ) :
    Function.Periodic (contourC1CrossLogIntegral Z W) (2 * Real.pi) :=
  periodic_contourCrossLogIntegral (ContourC1Space.periodic_lift Z)

def contourCrossLogOnCircle {γ : ℝ≥0} (Z W : ContourC1Space γ) : ContourCircle → ℂ :=
  (periodic_contourC1CrossLogIntegral Z W).lift

@[simp] theorem contourCrossLogOnCircle_coe {γ : ℝ≥0} (Z W : ContourC1Space γ) (θ : ℝ) :
    contourCrossLogOnCircle Z W (θ : ContourCircle) = contourC1CrossLogIntegral Z W θ := rfl

theorem continuous_contourCrossLogOnCircle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    Continuous (contourCrossLogOnCircle Z W) := by
  have hd : Differentiable ℝ (contourC1CrossLogIntegral Z W) :=
    fun θ => (hasDerivAt_contourC1CrossLogIntegral hγ1 Z W hσ hsep θ).differentiableAt
  exact continuous_periodicContourLift (periodic_contourC1CrossLogIntegral Z W) hd.continuous

def contourCrossLogBCF {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨contourCrossLogOnCircle Z W, continuous_contourCrossLogOnCircle hγ1 Z W hσ hsep⟩

def contourCrossLogC1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt (contourCrossLogBCF hγ1 Z W hσ hsep)
    (contourCrossLogDerivativeHolder hγ1 Z W hσ hsep)
    (hasDerivAt_contourC1CrossLogIntegral hγ1 Z W hσ hsep)

@[simp] theorem lift_contourCrossLogC1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    ContourC1Space.lift γ (contourCrossLogC1 hγ1 Z W hσ hsep) = contourC1CrossLogIntegral Z W := rfl

@[simp] theorem derivative_contourCrossLogC1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ) :
    ContourC1Space.derivative γ (contourCrossLogC1 hγ1 Z W hσ hsep) =
      contourCrossLogDerivativeHolder hγ1 Z W hσ hsep := rfl

def contourCrossLogValueBound (σ M : ℝ) : ℝ :=
  (2 * Real.pi) * (M * (|Real.log σ| + |Real.log (2 * M + 1)|))

theorem norm_contourC1CrossLogIntegral_le {γ : ℝ≥0}
    (Z W : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) (θ : ℝ) :
    ‖contourC1CrossLogIntegral Z W θ‖ ≤ contourCrossLogValueBound σ M := by
  have hb (φ : ℝ) :
      ‖contourCrossLogIntegrand (ContourC1Space.lift γ Z) (ContourC1Space.lift γ W)
        (deriv (ContourC1Space.lift γ W)) θ φ‖ ≤ M * (|Real.log σ| + |Real.log (2 * M + 1)|) := by
    have hl := hsep (θ : ContourCircle) (φ : ContourCircle)
    change σ ≤ ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ at hl
    have hu : ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖ ≤ 2 * M + 1 := by
      have hn := norm_sub_le (ContourC1Space.lift γ Z θ) (ContourC1Space.lift γ W φ)
      have hZ := (ContourC1Space.norm_eval_le Z (θ : ContourCircle)).trans hZM
      have hW := (ContourC1Space.norm_eval_le W (φ : ContourCircle)).trans hWM
      change ‖ContourC1Space.lift γ Z θ‖ ≤ M at hZ
      change ‖ContourC1Space.lift γ W φ‖ ≤ M at hW
      linarith
    have hlog : |Real.log ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ W φ‖| ≤
        |Real.log σ| + |Real.log (2 * M + 1)| := by
      simpa only [mul_one, Real.log_one, abs_zero, add_zero] using
        abs_log_le_of_mul_lower hσ (by norm_num : (0 : ℝ) < 1) (by simpa only [mul_one] using hl) hu
    rw [contourCrossLogIntegrand, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hlog ((ContourC1Space.norm_deriv_lift_le W φ).trans hWM)
      (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
  unfold contourC1CrossLogIntegral contourCrossLogIntegral
  calc
    _ ≤ ∫ φ in Icc (-Real.pi) Real.pi, M * (|Real.log σ| + |Real.log (2 * M + 1)|) := by
      apply norm_integral_le_of_norm_le (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [] with φ
      exact hb φ
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), intervalIntegral.integral_const]
      unfold contourCrossLogValueBound
      simp only [smul_eq_mul]
      ring

theorem norm_contourCrossLogC1_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : ContourC1Space γ) {σ M : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z W σ)
    (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourCrossLogC1 hγ1 Z W hσ hsep‖ ≤
      max (contourCrossLogValueBound σ M) (contourCrossLogDerivativeBound (γ : ℝ) σ M) := by
  have hb := norm_contourC1CrossLogIntegral_le Z W hσ hsep hM hZM hWM
  have hV : 0 ≤ contourCrossLogValueBound σ M := (norm_nonneg _).trans (hb 0)
  have hf : ‖contourCrossLogBCF hγ1 Z W hσ hsep‖ ≤ contourCrossLogValueBound σ M := by
    apply (BoundedContinuousFunction.norm_le hV).mpr
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact hb θ
  change max ‖contourCrossLogBCF hγ1 Z W hσ hsep‖ ‖contourCrossLogDerivativeHolder hγ1 Z W hσ hsep‖ ≤ _
  exact max_le_max hf (norm_contourCrossLogDerivativeHolder_le hγ1 Z W hσ hsep hM hZM hWM)

end Euler2D

end
