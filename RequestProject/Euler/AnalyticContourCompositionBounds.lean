module

public import RequestProject.Euler.AnalyticContourComposition

/-! Actual C1 Hölder shape estimates for a holomorphic spatial
field composed with the target contour. All spatial difference
bounds follow from genuine derivatives on the intervening segments. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

theorem norm_analytic_sub_le_on_segment {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) {B : ℝ} (hB : ∀ z ∈ U, ‖deriv F z‖ ≤ B)
    {a b : ℂ} (hseg : segment ℝ a b ⊆ U) : ‖F a - F b‖ ≤ B * ‖a - b‖ := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hF z (hseg hz)).differentiableAt)
    (fun z hz => hB z (hseg hz)) (convex_segment a b)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [norm_sub_rev] using hb

theorem lipschitz_analyticDerivative_composition_sub
    {γ : ℝ≥0} {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z W : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U)
    (hW : ∀ x, ContourC1Space.toBCF γ W x ∈ U)
    {B₂ B₃ M : ℝ} (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hM : 0 ≤ M)
    (hZM : ‖Z‖ ≤ M)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃)
    (hseg : ∀ x, segment ℝ (ContourC1Space.toBCF γ Z x) (ContourC1Space.toBCF γ W x) ⊆ U) :
    LipschitzWith (⟨(B₃ * M + B₂) * ‖Z - W‖, by positivity⟩ : ℝ≥0)
      (fun x => deriv F (ContourC1Space.toBCF γ Z x) - deriv F (ContourC1Space.toBCF γ W x)) := by
  apply lipschitzWith_contour_of_deriv_bound
    ((contDiff_analytic_comp_contour hF.deriv Z hZ).sub (contDiff_analytic_comp_contour hF.deriv W hW))
  intro θ
  have hd := (hasDerivAt_analytic_comp_contour hF.deriv Z hZ θ).sub
    (hasDerivAt_analytic_comp_contour hF.deriv W hW θ)
  have hd' : deriv (fun t => deriv F (ContourC1Space.lift γ Z t) -
      deriv F (ContourC1Space.lift γ W t)) θ =
      deriv (deriv F) (ContourC1Space.lift γ Z θ) * ContourC1Space.derivative γ Z (θ : ContourCircle) -
        deriv (deriv F) (ContourC1Space.lift γ W θ) * ContourC1Space.derivative γ W (θ : ContourCircle) := hd.deriv
  change ‖deriv (fun t => deriv F (ContourC1Space.lift γ Z t) -
    deriv F (ContourC1Space.lift γ W t)) θ‖ ≤ _
  rw [hd']
  let z := ContourC1Space.lift γ Z θ
  let w := ContourC1Space.lift γ W θ
  let dz := ContourC1Space.derivative γ Z (θ : ContourCircle)
  let dw := ContourC1Space.derivative γ W (θ : ContourCircle)
  have hdiff : ‖deriv (deriv F) z - deriv (deriv F) w‖ ≤ B₃ * ‖Z - W‖ := by
    exact (norm_analytic_sub_le_on_segment hF.deriv.deriv h₃ (hseg (θ : ContourCircle))).trans
      (mul_le_mul_of_nonneg_left (ContourC1Space.norm_eval_le (Z - W) (θ : ContourCircle)) hB₃)
  have hdz : ‖dz‖ ≤ M := (ContourC1Space.norm_derivativeEval_le Z _).trans hZM
  have hdd : ‖dz - dw‖ ≤ ‖Z - W‖ := ContourC1Space.norm_derivativeEval_le (Z - W) _
  have hfw : ‖deriv (deriv F) w‖ ≤ B₂ := h₂ w (hW (θ : ContourCircle))
  change ‖deriv (deriv F) z * dz - deriv (deriv F) w * dw‖ ≤ _
  calc
    _ = ‖(deriv (deriv F) z - deriv (deriv F) w) * dz + deriv (deriv F) w * (dz - dw)‖ := by
      congr 1; ring
    _ ≤ ‖deriv (deriv F) z - deriv (deriv F) w‖ * ‖dz‖ + ‖deriv (deriv F) w‖ * ‖dz - dw‖ := by
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ (B₃ * ‖Z - W‖) * M + B₂ * ‖Z - W‖ :=
      add_le_add (mul_le_mul hdiff hdz (norm_nonneg _) (by positivity))
        (mul_le_mul hfw hdd (norm_nonneg _) hB₂)
    _ = _ := by
      change (B₃ * ‖Z - W‖) * M + B₂ * ‖Z - W‖ = (B₃ * M + B₂) * ‖Z - W‖
      ring

theorem norm_analyticContourDerivativeHolder_sub_le
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z W : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U)
    (hW : ∀ x, ContourC1Space.toBCF γ W x ∈ U)
    {B₂ B₃ M : ℝ} (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hM : 0 ≤ M) (hZM : ‖Z‖ ≤ M)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃)
    (hseg : ∀ x, segment ℝ (ContourC1Space.toBCF γ Z x) (ContourC1Space.toBCF γ W x) ⊆ U) :
    ‖analyticContourDerivativeHolder hγ1 hF Z hZ hB₂ (fun x => h₂ _ (hZ x)) -
      analyticContourDerivativeHolder hγ1 hF W hW hB₂ (fun x => h₂ _ (hW x))‖ ≤
      (B₂ + Real.pi ^ (1 - (γ : ℝ)) * (B₃ * M + B₂)) * ‖Z - W‖ := by
  have hP : 0 ≤ Real.pi ^ (1 - (γ : ℝ)) := Real.rpow_nonneg Real.pi_pos.le _
  apply norm_contourHolder_le_of_bounds _ (by positivity)
  · intro x
    change ‖deriv F (ContourC1Space.toBCF γ Z x) - deriv F (ContourC1Space.toBCF γ W x)‖ ≤ _
    have hh := (norm_analytic_sub_le_on_segment hF.deriv h₂ (hseg x)).trans
      (mul_le_mul_of_nonneg_left (ContourC1Space.norm_eval_le (Z - W) x) hB₂)
    nlinarith [mul_nonneg (mul_nonneg hP (show 0 ≤ B₃ * M + B₂ by positivity)) (norm_nonneg (Z - W))]
  · intro x y
    change ‖(deriv F (ContourC1Space.toBCF γ Z x) - deriv F (ContourC1Space.toBCF γ W x)) -
      (deriv F (ContourC1Space.toBCF γ Z y) - deriv F (ContourC1Space.toBCF γ W y))‖ ≤ _
    have hh := (lipschitz_analyticDerivative_composition_sub hF Z W hZ hW hB₂ hB₃ hM hZM h₂ h₃ hseg).dist_le_mul x y
    rw [dist_eq_norm] at hh
    have hdist := mul_le_mul_of_nonneg_left (contour_dist_le_holder_power hγ1 x y)
      (show 0 ≤ (B₃ * M + B₂) * ‖Z - W‖ by positivity)
    have hb := hh.trans hdist
    nlinarith [mul_nonneg (mul_nonneg hB₂ (norm_nonneg (Z - W)))
      (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) (γ : ℝ))]

def analyticCompositionShapeConstant (γ M B₁ B₂ B₃ : ℝ) : ℝ :=
  B₁ + 2 * (B₁ + Real.pi ^ (1 - γ) * B₂ * M +
    (B₂ + Real.pi ^ (1 - γ) * (B₃ * M + B₂)) * M)

theorem norm_analyticContourComposition_sub_le
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (Z W : ContourC1Space γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U)
    (hW : ∀ x, ContourC1Space.toBCF γ W x ∈ U)
    {B₁ B₂ B₃ M : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hM : 0 ≤ M)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃)
    (hseg : ∀ x, segment ℝ (ContourC1Space.toBCF γ Z x) (ContourC1Space.toBCF γ W x) ⊆ U) :
    ‖analyticContourComposition hγ1 hF Z hZ hB₂ (fun x => h₂ _ (hZ x)) -
      analyticContourComposition hγ1 hF W hW hB₂ (fun x => h₂ _ (hW x))‖ ≤
      analyticCompositionShapeConstant (γ : ℝ) M B₁ B₂ B₃ * ‖Z - W‖ := by
  let A := analyticContourDerivativeHolder hγ1 hF Z hZ hB₂ (fun x => h₂ _ (hZ x))
  let B := analyticContourDerivativeHolder hγ1 hF W hW hB₂ (fun x => h₂ _ (hW x))
  let d := ‖Z - W‖
  let p := Real.pi ^ (1 - (γ : ℝ))
  let H := B₂ + p * (B₃ * M + B₂)
  have hp : 0 ≤ p := Real.rpow_nonneg Real.pi_pos.le _
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hAn : ‖A‖ ≤ B₁ + p * B₂ * M := by
    have hh := norm_analyticContourDerivativeHolder_le hγ1 hF Z hZ hB₁ hB₂
      (fun x => h₁ _ (hZ x)) (fun x => h₂ _ (hZ x))
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hZM (mul_nonneg hp hB₂)])
  have hAB : ‖A - B‖ ≤ H * d := norm_analyticContourDerivativeHolder_sub_le hγ1 hF Z W hZ hW
    hB₂ hB₃ hM hZM h₂ h₃ hseg
  have hval : ‖ContourC1Space.toBCF γ
      (analyticContourComposition hγ1 hF Z hZ hB₂ (fun x => h₂ _ (hZ x)) -
       analyticContourComposition hγ1 hF W hW hB₂ (fun x => h₂ _ (hW x)))‖ ≤ B₁ * d := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hB₁ (norm_nonneg _))).mpr
    intro x
    change ‖F (ContourC1Space.toBCF γ Z x) - F (ContourC1Space.toBCF γ W x)‖ ≤ _
    exact (norm_analytic_sub_le_on_segment hF h₁ (hseg x)).trans
      (mul_le_mul_of_nonneg_left (ContourC1Space.norm_eval_le (Z - W) x) hB₁)
  have hder : ‖HolderFunctionSpace.pointwiseMul A (ContourC1Space.derivative γ Z) -
      HolderFunctionSpace.pointwiseMul B (ContourC1Space.derivative γ W)‖ ≤
      (2 * (B₁ + p * B₂ * M) + 2 * H * M) * d := by
    have he : HolderFunctionSpace.pointwiseMul A (ContourC1Space.derivative γ Z) -
        HolderFunctionSpace.pointwiseMul B (ContourC1Space.derivative γ W) =
        HolderFunctionSpace.pointwiseMul A (ContourC1Space.derivative γ (Z - W)) +
          HolderFunctionSpace.pointwiseMul (A - B) (ContourC1Space.derivative γ W) := by
      apply HolderFunctionSpace.ext
      intro x
      change A x * ContourC1Space.derivative γ Z x - B x * ContourC1Space.derivative γ W x =
        A x * (ContourC1Space.derivative γ Z x - ContourC1Space.derivative γ W x) +
          (A x - B x) * ContourC1Space.derivative γ W x
      ring
    rw [he]
    calc
      _ ≤ ‖HolderFunctionSpace.pointwiseMul A (ContourC1Space.derivative γ (Z - W))‖ +
          ‖HolderFunctionSpace.pointwiseMul (A - B) (ContourC1Space.derivative γ W)‖ := norm_add_le _ _
      _ ≤ (2 * ‖A‖ * ‖ContourC1Space.derivative γ (Z - W)‖) +
          (2 * ‖A - B‖ * ‖ContourC1Space.derivative γ W‖) :=
        add_le_add (HolderFunctionSpace.norm_pointwiseMul_le _ _) (HolderFunctionSpace.norm_pointwiseMul_le _ _)
      _ ≤ 2 * (B₁ + p * B₂ * M) * d + 2 * (H * d) * M :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hAn (by norm_num))
            (ContourC1Space.norm_derivative_le (Z - W)) (norm_nonneg _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hAB (by norm_num))
            ((ContourC1Space.norm_derivative_le W).trans hWM) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  change max ‖ContourC1Space.toBCF γ
      (analyticContourComposition hγ1 hF Z hZ hB₂ (fun x => h₂ _ (hZ x)) -
       analyticContourComposition hγ1 hF W hW hB₂ (fun x => h₂ _ (hW x)))‖
      ‖HolderFunctionSpace.pointwiseMul A (ContourC1Space.derivative γ Z) -
        HolderFunctionSpace.pointwiseMul B (ContourC1Space.derivative γ W)‖ ≤ _
  apply max_le
  · refine hval.trans ?_
    dsimp only [analyticCompositionShapeConstant, H, p] at *
    nlinarith [mul_nonneg (show 0 ≤ 2 * (B₁ + p * B₂ * M + H * M) by positivity) (norm_nonneg (Z - W))]
  · refine hder.trans ?_
    dsimp only [analyticCompositionShapeConstant]
    change _ ≤ (B₁ + 2 * (B₁ + p * B₂ * M + H * M)) * d
    nlinarith [mul_nonneg hB₁ (norm_nonneg (Z - W))]

end Euler2D

end
