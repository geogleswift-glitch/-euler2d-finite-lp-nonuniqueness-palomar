module

public import RequestProject.Euler.ActualTorusContourCorrection
public import RequestProject.Euler.CircularPhysicalContourLittle

/-! The actual periodic-minus-planar correction forcing belongs to
the original little contour space and retains the true cubic
contour-norm cancellation budget. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem exists_actualTorusKernelCorrection_contourLittle
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w : ℂ → ℝ, Integrable w → (∀ y, a < ‖y‖ → w y = 0) →
      (∫ y, w y) = 0 → (∀ y, w (I * y) = w y) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∃ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          ∫ y, w y • planeComplexEquiv
            (torusBiotSavartKernel (complexTorusPoint (LittleContourSpace.lift γ Z θ - y)) -
              kernelK (complexPhysicalPlane (LittleContourSpace.lift γ Z θ - y)))) ∧
        ‖Q‖ / R ≤ K * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := by
  obtain ⟨K, hK, hC1⟩ := exists_actualTorusKernelCorrection_contourC1 ha ha16
  obtain ⟨K', hK', hpoint⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  refine ⟨K, hK, ?_⟩
  intro γ hγ1 w hw hsupp hmass hsym R L hR hL hsmall Z hZ
  obtain ⟨Q, hQ, hnorm⟩ := hC1 hγ1 w hw hsupp hmass hsym hR hL
    (hsmall.trans (by linarith)) Z.val hZ
  let F := fun z => conj (actualTorusCorrectionVelocity w z)
  let U : Set ℂ := ball 0 (a / 2)
  have hU : IsOpen U := isOpen_ball
  have hF : AnalyticOnNhd ℂ F U :=
    (analyticOnNhd_conj_actualTorusCorrectionVelocity ha ha16 hw hsupp hmass hsym).mono
      (ball_subset_ball (by linarith))
  have hZu : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U := by
    intro x
    have hx := (ContourC1Space.norm_eval_le Z.val x).trans hZ
    change ‖ContourC1Space.toBCF γ Z.val x‖ ≤ L * R at hx
    rw [mem_ball_zero_iff]
    nlinarith
  have hM : 0 ≤ ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := integral_nonneg (fun y => by positivity)
  let C := K' * a ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |w y|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB (m : ℕ) : 0 ≤ (m.factorial : ℝ) * C / (a / 2) ^ m := by positivity
  have hb (m : ℕ) : ∀ z ∈ U,
      ‖iteratedDeriv m F z‖ ≤ (m.factorial : ℝ) * C / (a / 2) ^ m := by
    intro z hz
    have hzn : ‖z‖ ≤ (1 : ℝ) * (a / 2) := by
      simpa only [one_mul] using (mem_ball_zero_iff.mp hz).le
    have hh := norm_iteratedDeriv_actualTorusCorrectionVelocity ha ha16 hK'.le (half_pos ha)
      (show (0 : ℝ) ≤ 1 by norm_num) (show ((1 : ℝ) + 1) * (a / 2) ≤ a by linarith)
      hw hsupp hmass hsym (hpoint w hw hsupp hsym hmass) hzn m
    have he : ((1 : ℝ) + 1) * (a / 2) = a := by ring
    rw [he] at hh
    exact hh
  have hQF : ∀ θ, ContourC1Space.lift γ Q θ = conj (F (LittleContourSpace.lift γ Z θ)) := by
    intro θ
    have hx := (ContourC1Space.norm_eval_le Z.val (θ : ContourCircle)).trans hZ
    change ‖ContourC1Space.lift γ Z.val θ‖ ≤ L * R at hx
    calc
      _ = actualTorusCorrectionVelocity w (ContourC1Space.lift γ Z.val θ) :=
        (hQ θ).trans (actualTorusKernelDifference_eq_correctionVelocity ha16 hsupp (by nlinarith))
      _ = _ := (conj_conj _).symm
  have hmem := contour_conjugate_analytic_composition_mem_little hγ1 hU hF Z hZu (hB 1) (hB 2) (hB 3)
    (by simpa only [iteratedDeriv_one] using hb 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 2)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 3) Q hQF
  exact ⟨⟨Q, hmem⟩, hQ, hnorm⟩

end Euler2D

end
