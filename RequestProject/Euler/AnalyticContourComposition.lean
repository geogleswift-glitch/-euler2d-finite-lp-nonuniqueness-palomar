module

public import RequestProject.Euler.ContourHolderValue

/-! A holomorphic spatial field evaluated on an actual C¹ Hölder
contour is an actual C¹ Hölder contour. The derivative is the true
chain-rule derivative, and the bound uses the first two spatial
derivatives rather than postulating a contour forcing norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

theorem hasDerivAt_analytic_comp_contour {γ : ℝ≥0} {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) (θ : ℝ) :
    HasDerivAt (fun t => F (ContourC1Space.lift γ Z t))
      (deriv F (ContourC1Space.lift γ Z θ) *
        ContourC1Space.derivative γ Z (θ : ContourCircle)) θ := by
  have hh := ((hF _ (hZ (θ : ContourCircle))).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    θ (ContourC1Space.hasDerivAt_lift Z θ)
  change HasDerivAt (fun t => F (ContourC1Space.lift γ Z t))
    ((ContourC1Space.derivative γ Z (θ : ContourCircle)) *
      deriv F (ContourC1Space.lift γ Z θ)) θ at hh
  simpa only [mul_comm] using hh

theorem continuous_analytic_comp_contour {γ : ℝ≥0} {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) :
    Continuous (fun x => F (ContourC1Space.toBCF γ Z x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hF _ (hZ x)).continuousAt.comp (ContourC1Space.toBCF γ Z).continuous.continuousAt

theorem contDiff_analytic_comp_contour {γ : ℝ≥0} {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) :
    ContDiff ℝ 1 (fun t => F (ContourC1Space.lift γ Z t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hc : ContDiffAt ℂ 1 F (ContourC1Space.lift γ Z θ) :=
    (hF _ (hZ (θ : ContourCircle))).contDiffAt
  exact (hc.restrict_scalars ℝ).comp θ
    (ContourC1Space.contDiff_lift Z).contDiffAt

theorem lipschitzWith_analyticDerivative_comp_contour {γ : ℝ≥0}
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) :
    LipschitzWith (⟨B₂ * ‖Z‖, mul_nonneg hB₂ (norm_nonneg Z)⟩ : ℝ≥0)
      (fun x => deriv F (ContourC1Space.toBCF γ Z x)) := by
  apply lipschitzWith_contour_of_deriv_bound
    (contDiff_analytic_comp_contour hF.deriv Z hZ)
  intro θ
  change ‖deriv (fun t => deriv F (ContourC1Space.lift γ Z t)) θ‖ ≤ B₂ * ‖Z‖
  rw [(hasDerivAt_analytic_comp_contour hF.deriv Z hZ θ).deriv, norm_mul]
  exact mul_le_mul (h₂ _) (ContourC1Space.norm_derivativeEval_le Z _)
    (norm_nonneg _) hB₂

def analyticContourDerivativeHolder {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) :
    ContourHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder
    (BoundedContinuousFunction.mkOfCompact
      ⟨_, continuous_analytic_comp_contour hF.deriv Z hZ⟩)
    (memHolder_contour_of_lipschitz (by exact_mod_cast hγ1)
      (lipschitzWith_analyticDerivative_comp_contour hF Z hZ hB₂ h₂))

@[simp] theorem analyticContourDerivativeHolder_apply {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) (x : ContourCircle) :
    analyticContourDerivativeHolder hγ1 hF Z hZ hB₂ h₂ x =
      deriv F (ContourC1Space.toBCF γ Z x) := rfl

theorem norm_analyticContourDerivativeHolder_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ x, ‖deriv F (ContourC1Space.toBCF γ Z x)‖ ≤ B₁)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) :
    ‖analyticContourDerivativeHolder hγ1 hF Z hZ hB₂ h₂‖ ≤
      B₁ + Real.pi ^ (1 - (γ : ℝ)) * B₂ * ‖Z‖ := by
  have hP : 0 ≤ Real.pi ^ (1 - (γ : ℝ)) := Real.rpow_nonneg Real.pi_pos.le _
  apply norm_contourHolder_le_of_bounds _ (by positivity)
  · intro x
    exact (h₁ x).trans (le_add_of_nonneg_right (by positivity))
  · intro x y
    have hl := (lipschitzWith_analyticDerivative_comp_contour hF Z hZ hB₂ h₂).dist_le_mul x y
    change ‖deriv F (ContourC1Space.toBCF γ Z x) - deriv F (ContourC1Space.toBCF γ Z y)‖ ≤ _
    have hh : ‖deriv F (ContourC1Space.toBCF γ Z x) - deriv F (ContourC1Space.toBCF γ Z y)‖ ≤
        (B₂ * ‖Z‖) * dist x y := by simpa only [dist_eq_norm] using hl
    calc
      _ ≤ (B₂ * ‖Z‖) * (Real.pi ^ (1 - (γ : ℝ)) * dist x y ^ (γ : ℝ)) :=
        hh.trans (mul_le_mul_of_nonneg_left (contour_dist_le_holder_power hγ1 x y) (by positivity))
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) (γ : ℝ)]

def analyticContourComposition {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) :
    ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_analytic_comp_contour hF Z hZ⟩)
    (HolderFunctionSpace.pointwiseMul
      (analyticContourDerivativeHolder hγ1 hF Z hZ hB₂ h₂) (ContourC1Space.derivative γ Z))
    (fun θ => hasDerivAt_analytic_comp_contour hF Z hZ θ)

@[simp] theorem lift_analyticContourComposition {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) (θ : ℝ) :
    ContourC1Space.lift γ (analyticContourComposition hγ1 hF Z hZ hB₂ h₂) θ =
      F (ContourC1Space.lift γ Z θ) := rfl

theorem norm_analyticContourComposition_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (Z : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) {B₀ B₁ B₂ : ℝ}
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₀ : ∀ x, ‖F (ContourC1Space.toBCF γ Z x)‖ ≤ B₀)
    (h₁ : ∀ x, ‖deriv F (ContourC1Space.toBCF γ Z x)‖ ≤ B₁)
    (h₂ : ∀ x, ‖deriv (deriv F) (ContourC1Space.toBCF γ Z x)‖ ≤ B₂) :
    ‖analyticContourComposition hγ1 hF Z hZ hB₂ h₂‖ ≤
      max B₀ (2 * (B₁ + Real.pi ^ (1 - (γ : ℝ)) * B₂ * ‖Z‖) * ‖Z‖) := by
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hB₀).mpr h₀
  · refine (HolderFunctionSpace.norm_pointwiseMul_le _ _).trans ?_
    have hh := norm_analyticContourDerivativeHolder_le hγ1 hF Z hZ hB₁ hB₂ h₁ h₂
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2))
      (ContourC1Space.norm_derivative_le Z) (norm_nonneg _)
      (by positivity)

end Euler2D

end
