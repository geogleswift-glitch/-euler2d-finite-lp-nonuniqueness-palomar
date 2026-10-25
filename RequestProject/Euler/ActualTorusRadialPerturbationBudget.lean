module

public import RequestProject.Euler.ActualTorusRadialReference
public import RequestProject.Euler.ActualTorusContourSourceContinuity
public import RequestProject.Euler.UniformActualTorusContourBudget

/-! A uniform original Little-norm budget for the actual periodic
velocity in terms of its perturbation from a radial zero-mass source.
The reference correction is exactly zero. The remaining fourth
absolute moment therefore belongs to the perturbation itself. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_uniform_actualTorusCorrection_radialPerturbation_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ}, 0 < a → a ≤ 1 / 16 →
      ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w v : ℂ → ℝ, Integrable w → Integrable v →
      (∀ y, a < ‖y‖ → w y = 0) → (∀ y, a < ‖y‖ → v y = 0) →
      (∫ y, w y) = 0 → (∫ y, v y) = 0 →
      (∀ y, w (I * y) = w y) →
      (∀ (θ : ℝ) (y : ℂ), v (exp ((θ : ℂ) * I) * y) = v y) →
      ∀ {r L : ℝ}, 0 < r → 0 ≤ L → (L + 1) * r ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * r →
      ∀ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) →
        ‖Q‖ / r ≤ C * torusCorrectionContourBudget (γ : ℝ) L * r ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y - v y| := by
  obtain ⟨C, hC, hbudget⟩ := exists_uniform_actualTorusCorrection_contourLittle_budget
  refine ⟨C, hC, ?_⟩
  intro a ha ha16 γ hγ w v hw hv hws hvs hwm hvm hwy hvr r L hr hL hsmall Z hZ Q hQ
  have hds : ∀ y, a < ‖y‖ → w y - v y = 0 := by
    intro y hy
    rw [hws y hy, hvs y hy, sub_self]
  have hdm : (∫ y, w y - v y) = 0 := by
    rw [integral_sub hw hv, hwm, hvm, sub_self]
  have hvy : ∀ y, v (I * y) = v y := by
    intro y
    have hh := hvr (Real.pi / 2) y
    rw [show (((Real.pi / 2 : ℝ) : ℂ) * I) = (Real.pi / 2 : ℂ) * I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I] at hh
    exact hh
  have hdy : ∀ y, w (I * y) - v (I * y) = w y - v y := by
    intro y
    rw [hwy y, hvy y]
  have hQd : ∀ θ, LittleContourSpace.lift γ Q θ =
      actualTorusCorrectionVelocity (fun y => w y - v y) (LittleContourSpace.lift γ Z θ) := by
    intro θ
    have hx : ‖LittleContourSpace.lift γ Z θ‖ ≤ a := by
      have hh := (LittleContourSpace.norm_eval_le Z (θ : ContourCircle)).trans hZ
      change ‖LittleContourSpace.lift γ Z θ‖ ≤ L * r at hh
      nlinarith only [hh, hsmall, hr, ha]
    rw [actualTorusCorrectionVelocity_sub hw hv,
      actualTorusCorrectionVelocity_radial_zero ha ha16 hv hvs hvr hvm hx, sub_zero]
    exact hQ θ
  exact hbudget ha ha16 hγ (fun y => w y - v y) (hw.sub hv) hds hdm hdy
    hr hL hsmall Z hZ Q hQd

theorem exists_uniform_actualTorusCorrection_radialPerturbation_contourLittle :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ}, 0 < a → a ≤ 1 / 16 →
      ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w v : ℂ → ℝ, Integrable w → Integrable v →
      (∀ y, a < ‖y‖ → w y = 0) → (∀ y, a < ‖y‖ → v y = 0) →
      (∫ y, w y) = 0 → (∫ y, v y) = 0 →
      (∀ y, w (I * y) = w y) →
      (∀ (θ : ℝ) (y : ℂ), v (exp ((θ : ℂ) * I) * y) = v y) →
      ∀ {r L : ℝ}, 0 < r → 0 ≤ L → (L + 1) * r ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * r →
      ∃ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) ∧
        ‖Q‖ / r ≤ C * torusCorrectionContourBudget (γ : ℝ) L * r ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y - v y| := by
  obtain ⟨C, hC, hbudget⟩ := exists_uniform_actualTorusCorrection_radialPerturbation_budget
  refine ⟨C, hC, ?_⟩
  intro a ha ha16 γ hγ w v hw hv hws hvs hwm hvm hwy hvr r L hr hL hsmall Z hZ
  obtain ⟨_Cs, _hCs, hsource⟩ := exists_actualTorusKernelCorrection_contourLittle ha ha16
  obtain ⟨Q, hQ, _hn⟩ := hsource hγ w hw hws hwm hwy hr hL hsmall Z hZ
  have hQactual : ∀ θ, LittleContourSpace.lift γ Q θ =
      actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ) := by
    intro θ
    have hx : ‖LittleContourSpace.lift γ Z θ‖ ≤ a := by
      have hh := (LittleContourSpace.norm_eval_le Z (θ : ContourCircle)).trans hZ
      change ‖LittleContourSpace.lift γ Z θ‖ ≤ L * r at hh
      nlinarith only [hh, hsmall, hr, ha]
    exact (hQ θ).trans (actualTorusKernelDifference_eq_correctionVelocity ha16 hws hx)
  exact ⟨Q, hQactual, hbudget ha ha16 hγ w v hw hv hws hvs hwm hvm hwy hvr
    hr hL hsmall Z hZ Q hQactual⟩

end Euler2D

end
