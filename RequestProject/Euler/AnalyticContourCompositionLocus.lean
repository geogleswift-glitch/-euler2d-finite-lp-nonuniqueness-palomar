module

public import RequestProject.Euler.AnalyticContourCompositionLittle

/-! Actual local Lipschitz dependence of analytic physical forcing
on its target in both the original C1 Hölder and little spaces. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

abbrev AnalyticContourTargetLocus (γ : ℝ≥0) (U : Set ℂ) :=
  {Z : ContourC1Space γ // ∀ x, ContourC1Space.toBCF γ Z x ∈ U}

def analyticContourCompositionOnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) {B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂) (Z : AnalyticContourTargetLocus γ U) : ContourC1Space γ :=
  analyticContourComposition hγ1 hF Z.val Z.property hB₂ (fun x => h₂ _ (Z.property x))

theorem locallyLipschitz_analyticContourCompositionOnLocus
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃) :
    LocallyLipschitz (analyticContourCompositionOnLocus hγ1 hF hB₂ h₂) := by
  intro Z
  obtain ⟨r, hr, hball⟩ := exists_contour_value_ball_neighborhood Z.val hU Z.property
  let R := min r 1
  have hR : 0 < R := lt_min hr zero_lt_one
  let M := ‖Z.val‖ + 1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let K := analyticCompositionShapeConstant (γ : ℝ) M B₁ B₂ B₃
  have hK : 0 ≤ K := by dsimp only [K, analyticCompositionShapeConstant]; positivity
  refine ⟨⟨K, hK⟩, Metric.ball Z R, Metric.ball_mem_nhds Z hR, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro W hW V hV
  have hWn : ‖W.val - Z.val‖ < R := by simpa only [Subtype.dist_eq, dist_eq_norm] using mem_ball.mp hW
  have hVn : ‖V.val - Z.val‖ < R := by simpa only [Subtype.dist_eq, dist_eq_norm] using mem_ball.mp hV
  have hWM : ‖W.val‖ ≤ M := by
    have hn := norm_le_norm_sub_add W.val Z.val
    have hd := hWn.trans_le (min_le_right r 1)
    dsimp only [M]
    linarith
  have hVM : ‖V.val‖ ≤ M := by
    have hn := norm_le_norm_sub_add V.val Z.val
    have hd := hVn.trans_le (min_le_right r 1)
    dsimp only [M]
    linarith
  have hWball (x : ContourCircle) : ContourC1Space.toBCF γ W.val x ∈
      Metric.ball (ContourC1Space.toBCF γ Z.val x) r := by
    rw [mem_ball, dist_eq_norm]
    exact (ContourC1Space.norm_eval_le (W.val - Z.val) x).trans_lt (hWn.trans_le (min_le_left r 1))
  have hVball (x : ContourCircle) : ContourC1Space.toBCF γ V.val x ∈
      Metric.ball (ContourC1Space.toBCF γ Z.val x) r := by
    rw [mem_ball, dist_eq_norm]
    exact (ContourC1Space.norm_eval_le (V.val - Z.val) x).trans_lt (hVn.trans_le (min_le_left r 1))
  have hseg (x : ContourCircle) : segment ℝ (ContourC1Space.toBCF γ W.val x)
      (ContourC1Space.toBCF γ V.val x) ⊆ U :=
    ((convex_ball _ _).segment_subset (hWball x) (hVball x)).trans (hball x)
  rw [dist_eq_norm]
  change ‖analyticContourCompositionOnLocus hγ1 hF hB₂ h₂ W -
      analyticContourCompositionOnLocus hγ1 hF hB₂ h₂ V‖ ≤ K * dist W.val V.val
  rw [dist_eq_norm]
  exact norm_analyticContourComposition_sub_le hγ1 hF W.val V.val W.property V.property
    hB₁ hB₂ hB₃ hM hWM hVM h₁ h₂ h₃ hseg

abbrev AnalyticLittleContourTargetLocus (γ : ℝ≥0) (U : Set ℂ) :=
  {Z : LittleContourSpace γ // ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U}

def analyticLittleTargetToC1 {γ : ℝ≥0} {U : Set ℂ}
    (Z : AnalyticLittleContourTargetLocus γ U) : AnalyticContourTargetLocus γ U :=
  ⟨Z.val.val, Z.property⟩

theorem isometry_analyticLittleTargetToC1 (γ : ℝ≥0) (U : Set ℂ) :
    Isometry (analyticLittleTargetToC1 (γ := γ) (U := U)) := by intro Z W; rfl

def analyticContourCompositionLittleOnLocus
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃)
    (Z : AnalyticLittleContourTargetLocus γ U) : LittleContourSpace γ :=
  analyticContourCompositionLittle hγ1 hU hF Z.val Z.property hB₁ hB₂ hB₃ h₁ h₂ h₃

theorem locallyLipschitz_analyticContourCompositionLittleOnLocus
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃) :
    LocallyLipschitz (analyticContourCompositionLittleOnLocus hγ1 hU hF hB₁ hB₂ hB₃ h₁ h₂ h₃) := by
  have hc : LocallyLipschitz (fun Z : AnalyticLittleContourTargetLocus γ U =>
      analyticContourCompositionOnLocus hγ1 hF hB₂ h₂ (analyticLittleTargetToC1 Z)) :=
    (locallyLipschitz_analyticContourCompositionOnLocus hγ1 hU hF hB₁ hB₂ hB₃ h₁ h₂ h₃).comp
      (isometry_analyticLittleTargetToC1 γ U).lipschitz.locallyLipschitz
  intro Z
  obtain ⟨K, V, hV, hLip⟩ := hc Z
  refine ⟨K, V, hV, ?_⟩
  intro W hW P hP
  exact hLip hW hP

end Euler2D

end
