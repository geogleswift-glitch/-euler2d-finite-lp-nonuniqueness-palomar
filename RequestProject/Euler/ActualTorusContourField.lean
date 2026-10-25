module

public import RequestProject.Euler.ActualTorusContourLittle
public import RequestProject.Euler.AnalyticContourCompositionLocus

/-! A genuine Little-space torus correction field on a fixed target ball.
Its Lipschitz constant is uniform over the actual source densities with
one common fourth absolute moment bound. This supplies the spatial
hypothesis of the nonautonomous contour existence theorem. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace Euler2D

theorem exists_actualTorusCorrection_LittleField {a M : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) (hM : 0 ≤ M)
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    ∃ K : ℝ≥0, ∀ (w : ℂ → ℝ), Integrable w →
      (∀ y, a < ‖y‖ → w y = 0) → (∫ y, w y) = 0 → (∀ y, w (I * y) = w y) →
      (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ≤ M →
      ∃ E : LittleContourSpace γ → LittleContourSpace γ,
        (∀ Z, ‖Z‖ < a / 4 → ∀ θ,
          LittleContourSpace.lift γ (E Z) θ =
            actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) ∧
        LipschitzOnWith K E (ball 0 (a / 4)) := by
  obtain ⟨C, hC, hpoint⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  let B (m : ℕ) : ℝ := (m.factorial : ℝ) * (C * a ^ 3 * M) / (a / 2) ^ m
  have hB (m : ℕ) : 0 ≤ B m := by dsimp only [B]; positivity
  let L : ℝ := analyticCompositionShapeConstant (γ : ℝ) (a / 4) (B 1) (B 2) (B 3)
  have hL : 0 ≤ L := by dsimp only [L, analyticCompositionShapeConstant]; positivity
  refine ⟨⟨L, hL⟩, ?_⟩
  intro w hw hsupp hmass hsym hwM
  let F := fun z => conj (actualTorusCorrectionVelocity w z)
  let U : Set ℂ := ball 0 (a / 2)
  have hF : AnalyticOnNhd ℂ F U :=
    (analyticOnNhd_conj_actualTorusCorrectionVelocity ha ha16 hw hsupp hmass hsym).mono
      (ball_subset_ball (by linarith))
  have hb (m : ℕ) : ∀ z ∈ U, ‖iteratedDeriv m F z‖ ≤ B m := by
    intro z hz
    have hzn : ‖z‖ ≤ (1 : ℝ) * (a / 2) := by
      simpa only [one_mul] using (mem_ball_zero_iff.mp hz).le
    have hh := norm_iteratedDeriv_actualTorusCorrectionVelocity ha ha16 hC.le (half_pos ha)
      (show (0 : ℝ) ≤ 1 by norm_num) (show ((1 : ℝ) + 1) * (a / 2) ≤ a by linarith)
      hw hsupp hmass hsym (hpoint w hw hsupp hsym hmass) hzn m
    rw [show ((1 : ℝ) + 1) * (a / 2) = a by ring] at hh
    refine hh.trans ?_
    dsimp only [B]
    gcongr
  have h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B 1 := by simpa only [iteratedDeriv_one] using hb 1
  have h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 2
  have h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B 3 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 3
  have htarget (Z : LittleContourSpace γ) (hZ : ‖Z‖ < a / 4) :
      ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U := by
    intro x
    rw [mem_ball_zero_iff]
    have hn := ContourC1Space.norm_eval_le Z.val x
    change ‖ContourC1Space.toBCF γ Z.val x‖ ≤ ‖Z‖ at hn
    exact hn.trans_lt (hZ.trans (by linarith))
  let Q (Z : LittleContourSpace γ) (hZ : ‖Z‖ < a / 4) : LittleContourSpace γ :=
    analyticContourCompositionLittle hγ1 isOpen_ball hF Z (htarget Z hZ)
      (hB 1) (hB 2) (hB 3) h₁ h₂ h₃
  let E : LittleContourSpace γ → LittleContourSpace γ := fun Z =>
    if hZ : ‖Z‖ < a / 4 then contourLittleConjugate (Q Z hZ) else 0
  refine ⟨E, ?_, ?_⟩
  · intro Z hZ θ
    dsimp only [E]
    rw [dif_pos hZ, lift_contourLittleConjugate]
    change conj (F (LittleContourSpace.lift γ Z θ)) = _
    exact conj_conj _
  · apply LipschitzOnWith.of_dist_le_mul
    intro Z hZ W hW
    have hZn : ‖Z‖ < a / 4 := mem_ball_zero_iff.mp hZ
    have hWn : ‖W‖ < a / 4 := mem_ball_zero_iff.mp hW
    have heZ : E Z = contourLittleConjugate (Q Z hZn) := dif_pos hZn
    have heW : E W = contourLittleConjugate (Q W hWn) := dif_pos hWn
    rw [dist_eq_norm, heZ, heW, dist_eq_norm]
    have he : ((contourLittleConjugate (Q Z hZn)) - (contourLittleConjugate (Q W hWn))).val =
        contourC1Conjugate ((Q Z hZn).val - (Q W hWn).val) := by
      change contourC1ConjugateCLM γ (Q Z hZn).val - contourC1ConjugateCLM γ (Q W hWn).val =
        contourC1ConjugateCLM γ ((Q Z hZn).val - (Q W hWn).val)
      exact (map_sub _ _ _).symm
    change ‖((contourLittleConjugate (Q Z hZn)) - (contourLittleConjugate (Q W hWn))).val‖ ≤ _
    rw [he]
    refine (norm_contourC1Conjugate_le _).trans ?_
    exact norm_analyticContourComposition_sub_le hγ1 hF Z.val W.val (htarget Z hZn) (htarget W hWn)
      (hB 1) (hB 2) (hB 3) (by positivity : 0 ≤ a / 4) hZn.le hWn.le h₁ h₂ h₃
      (fun x => (convex_ball _ _).segment_subset (htarget Z hZn x) (htarget W hWn x))

end Euler2D

end
