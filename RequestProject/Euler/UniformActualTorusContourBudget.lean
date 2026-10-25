module

public import RequestProject.Euler.ActualTorusContourFieldBudget

/-! The actual Little cubic budget has one constant for every sufficiently
small source radius. In particular the constant remains fixed when the
entire physical configuration is spatially shrunk. -/

@[expose] public section

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_uniform_actualTorusCorrection_contourLittle_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ}, 0 < a → a ≤ 1 / 16 →
      ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w : ℂ → ℝ, Integrable w → (∀ y, a < ‖y‖ → w y = 0) →
      (∫ y, w y) = 0 → (∀ y, w (I * y) = w y) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∀ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) →
        ‖Q‖ / R ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := by
  obtain ⟨C, hC, hbound⟩ := exists_actualTorusCorrection_contourLittle_budget
    (by norm_num : (0 : ℝ) < 1 / 16) (le_refl (1 / 16 : ℝ))
  refine ⟨C, hC, ?_⟩
  intro a _ ha16 γ hγ w hw hs hm hy R L hR hL hsmall Z hZ Q hQ
  exact hbound hγ w hw (fun y h => hs y (ha16.trans_lt h)) hm hy hR hL
    (by linarith) Z hZ Q hQ

end Euler2D

end
