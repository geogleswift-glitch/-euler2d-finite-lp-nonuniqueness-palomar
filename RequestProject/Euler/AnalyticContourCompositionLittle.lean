module

public import RequestProject.Euler.AnalyticContourCompositionBounds
public import RequestProject.Euler.ContourCrossLogLittle

/-! Genuine preservation of the original little contour space by
composition with an analytic physical field. Smooth target contours
approximate the actual target in the original Banach norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff BoundedContinuousFunction

namespace Euler2D

theorem exists_contour_value_ball_neighborhood {γ : ℝ≥0} (Z : ContourC1Space γ)
    {U : Set ℂ} (hU : IsOpen U) (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) :
    ∃ r > 0, ∀ x, Metric.ball (ContourC1Space.toBCF γ Z x) r ⊆ U := by
  have hc : IsCompact (range (ContourC1Space.toBCF γ Z)) :=
    isCompact_range (ContourC1Space.toBCF γ Z).continuous
  obtain ⟨r, hr, hsub⟩ := hc.exists_thickening_subset_open hU (by rintro y ⟨x, rfl⟩; exact hZ x)
  refine ⟨r, hr, ?_⟩
  intro x y hy
  apply hsub
  exact mem_thickening_iff.mpr ⟨ContourC1Space.toBCF γ Z x, mem_range_self x, mem_ball.mp hy⟩

theorem analyticContourComposition_mem_little
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (Z : LittleContourSpace γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃) :
    analyticContourComposition hγ1 hF Z.val hZ hB₂ (fun x => h₂ _ (hZ x)) ∈
      (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  obtain ⟨r, hr, hball⟩ := exists_contour_value_ball_neighborhood Z.val hU hZ
  obtain ⟨u, hsu, heu, hlimu⟩ := LittleContourSpace.exists_smooth_sequence_with_norm_error Z
    (lt_min hr zero_lt_one)
  have hnear (n : ℕ) : ‖(u n).val - Z.val‖ < min r 1 := (heu n).trans_le (min_le_left _ _)
  have huBall (n : ℕ) (x : ContourCircle) : ContourC1Space.toBCF γ (u n).val x ∈
      Metric.ball (ContourC1Space.toBCF γ Z.val x) r := by
    rw [mem_ball, dist_eq_norm]
    exact (ContourC1Space.norm_eval_le ((u n).val - Z.val) x).trans_lt
      ((hnear n).trans_le (min_le_left _ _))
  have huU (n : ℕ) (x : ContourCircle) : ContourC1Space.toBCF γ (u n).val x ∈ U := hball x (huBall n x)
  have hseg (n : ℕ) (x : ContourCircle) : segment ℝ (ContourC1Space.toBCF γ Z.val x)
      (ContourC1Space.toBCF γ (u n).val x) ⊆ U :=
    ((convex_ball _ _).segment_subset (mem_ball_self hr) (huBall n x)).trans (hball x)
  let M := ‖Z.val‖ + 1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hZM : ‖Z.val‖ ≤ M := by dsimp only [M]; linarith
  have huM (n : ℕ) : ‖(u n).val‖ ≤ M := by
    have hh := norm_le_norm_sub_add (u n).val Z.val
    have hd := (hnear n).trans_le (min_le_right _ _)
    dsimp only [M]
    linarith
  let C := analyticCompositionShapeConstant (γ : ℝ) M B₁ B₂ B₃
  let v : ℕ → ContourC1Space γ := fun n =>
    analyticContourComposition hγ1 hF (u n).val (huU n) hB₂ (fun x => h₂ _ (huU n x))
  let v₀ := analyticContourComposition hγ1 hF Z.val hZ hB₂ (fun x => h₂ _ (hZ x))
  have hvnorm (n : ℕ) : ‖v n - v₀‖ ≤ C * ‖(u n).val - Z.val‖ := by
    have hh := norm_analyticContourComposition_sub_le hγ1 hF Z.val (u n).val hZ (huU n)
      hB₁ hB₂ hB₃ hM hZM (huM n) h₁ h₂ h₃ (hseg n)
    calc
      ‖v n - v₀‖ = ‖v₀ - v n‖ := norm_sub_rev _ _
      _ ≤ C * ‖Z.val - (u n).val‖ := hh
      _ = C * ‖(u n).val - Z.val‖ := congrArg (fun d : ℝ => C * d) (norm_sub_rev _ _)
  have huval : Tendsto (fun n => (u n).val) atTop (𝓝 Z.val) :=
    ((LittleContourSpace.inclusion γ).continuous.tendsto Z).comp hlimu
  have hdist : Tendsto (fun n => ‖(u n).val - Z.val‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using (huval.sub (tendsto_const_nhds (x := Z.val))).norm
  have hvlim : Tendsto v atTop (𝓝 v₀) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hvnorm (by
      simpa only [mul_zero] using hdist.const_mul C)
  apply (isClosed_littleContourSpace γ).mem_of_tendsto hvlim
  apply Eventually.of_forall
  intro n
  have hs : ContDiff ℝ ∞ (ContourC1Space.lift γ (v n)) := by
    change ContDiff ℝ ∞ (fun θ => F (ContourC1Space.lift γ (u n).val θ))
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hc : ContDiffAt ℂ ∞ F (ContourC1Space.lift γ (u n).val θ) :=
      (hF _ (huU n (θ : ContourCircle))).contDiffAt
    exact (hc.restrict_scalars ℝ).comp θ (hsu n).contDiffAt
  exact (LittleContourSpace.ofSmooth γ (v n) hs).property

def analyticContourCompositionLittle
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (Z : LittleContourSpace γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃) : LittleContourSpace γ :=
  ⟨analyticContourComposition hγ1 hF Z.val hZ hB₂ (fun x => h₂ _ (hZ x)),
    analyticContourComposition_mem_little hγ1 hU hF Z hZ hB₁ hB₂ hB₃ h₁ h₂ h₃⟩

@[simp] theorem lift_analyticContourCompositionLittle
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (Z : LittleContourSpace γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃) :
    LittleContourSpace.lift γ (analyticContourCompositionLittle hγ1 hU hF Z hZ hB₁ hB₂ hB₃ h₁ h₂ h₃) =
      F ∘ LittleContourSpace.lift γ Z := rfl

end Euler2D

end
