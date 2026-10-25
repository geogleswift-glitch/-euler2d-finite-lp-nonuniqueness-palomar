module

public import RequestProject.Euler.CircularFourthMomentReferenceForcing

/-! The actual growing coordinate is controlled by pointwise contour
values. This allows the genuine exterior velocity remainder to be
projected without first estimating its full Holder derivative norm. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) pointwiseProjectionLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) pointwiseProjectionLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem norm_littleContourFourierCoefficient_le_of_lift_bound {γ : ℝ≥0}
    (k : ℤ) (H : LittleContourSpace γ) {B : ℝ}
    (hH : ∀ θ : ℝ, ‖LittleContourSpace.lift γ H θ‖ ≤ B) :
    ‖littleContourFourierCoefficient γ k H‖ ≤ B := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hI : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ‖ ≤ B * (2 * Real.pi) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := B)
      (f := fun θ : ℝ => LittleContourSpace.lift γ H θ * contourCircleCharacter (-k) θ)
      (fun θ _ => by rw [norm_mul, norm_contourCircleCharacter, mul_one]; exact hH θ)
    simpa only [sub_zero, abs_of_pos hp] using hb
  unfold littleContourFourierCoefficient
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (B * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hp.le)
    _ = B := by field_simp

theorem norm_circularUnstableCoordinate_le_of_lift_bound {γ : ℝ≥0}
    (H : Fin 2 → LittleContourSpace γ) {B : ℝ}
    (hH : ∀ i θ, ‖LittleContourSpace.lift γ (H i) θ‖ ≤ B) :
    ‖circularUnstableCoordinateCLM γ H‖ ≤ (2 / cellA) * B := by
  let η := (circularModeAmplitudeCoefficientCLM γ 2 H).1
  have hnormal (i : Fin 2) : ‖η i‖ ≤ (2 * B) / circularContourRadii i := by
    change ‖littleContourModeNormalCoefficientCLM γ (circularContourRadii i) 2 (H i)‖ ≤ _
    rw [littleContourModeNormalCoefficientCLM_apply, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (circularContourRadii_bounds i).1.le]
    apply div_le_div_of_nonneg_right _ (circularContourRadii_bounds i).1.le
    have hp := norm_littleContourFourierCoefficient_le_of_lift_bound 5 (H i) (hH i)
    have hm := norm_littleContourFourierCoefficient_le_of_lift_bound (-3) (H i) (hH i)
    exact (norm_add_le _ _).trans (by
      rw [norm_conj]
      norm_num at hp hm ⊢
      linarith only [hp, hm])
  have hη₀ : ‖η 0‖ ≤ (2 * B) / cellA := by simpa [circularContourRadii] using hnormal 0
  have hη₁ : ‖η 1‖ ≤ 2 * B := by simpa [circularContourRadii] using hnormal 1
  have hden : ‖(2 : ℂ) * I * (cellA : ℂ)‖ = 2 * cellA := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_of_nonneg cellA_pos.le]
  rw [circularUnstableCoordinate_eq_ellPlus_amplitude]
  change ‖η 0 / 2 + η 1 / (2 * I * cellA)‖ ≤ _
  calc
    _ ≤ ‖η 0 / 2‖ + ‖η 1 / (2 * I * cellA)‖ := norm_add_le _ _
    _ = ‖η 0‖ / 2 + ‖η 1‖ / (2 * cellA) := by rw [norm_div, norm_div, hden]; norm_num
    _ ≤ ((2 * B) / cellA) / 2 + (2 * B) / (2 * cellA) :=
      add_le_add (div_le_div_of_nonneg_right hη₀ (by norm_num))
        (div_le_div_of_nonneg_right hη₁ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) cellA_pos.le))
    _ = (2 / cellA) * B := by field_simp [cellA_pos.ne']; ring

theorem norm_circularUnstableCoordinate_sub_le_of_lift_bound {γ : ℝ≥0}
    (H G : Fin 2 → LittleContourSpace γ) {B : ℝ}
    (hH : ∀ i θ, ‖LittleContourSpace.lift γ (H i) θ - LittleContourSpace.lift γ (G i) θ‖ ≤ B) :
    ‖circularUnstableCoordinateCLM γ H - circularUnstableCoordinateCLM γ G‖ ≤ (2 / cellA) * B := by
  rw [← map_sub]
  apply norm_circularUnstableCoordinate_le_of_lift_bound
  intro i θ
  exact hH i θ

end Euler2D

end
