module

public import RequestProject.Euler.ContourRegularizedPatchBounds
public import RequestProject.Euler.LogLipschitz

/-! A uniform approximation estimate for the actual planar logarithmic
gradient. Splitting at radius r and choosing regularization r² gives a
common error of order r, without a domain-dependent dominating function. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

namespace Euler2D

theorem norm_regularizedLogGradient_zero_sub_square_far_le
    {r : ℝ} (hr : 0 < r) (x y : ℂ) (hfar : r ≤ ‖y - x‖) :
    ‖regularizedLogGradient x 0 y - regularizedLogGradient x (r ^ 2) y‖ ≤ r := by
  let n := ‖y - x‖
  have hn : 0 < n := hr.trans_le hfar
  have hden : 0 < n ^ 2 * ((r ^ 2) ^ 2 + n ^ 2) := by positivity
  have he : regularizedLogGradient x 0 y - regularizedLogGradient x (r ^ 2) y =
      ((r ^ 2) ^ 2 / (n ^ 2 * ((r ^ 2) ^ 2 + n ^ 2))) • (y - x) := by
    unfold regularizedLogGradient
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    rw [← sub_smul]
    congr 1
    change (n ^ 2)⁻¹ - ((r ^ 2) ^ 2 + n ^ 2)⁻¹ = _
    field_simp
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (r ^ 2) ^ 2 / (n ^ 2 * ((r ^ 2) ^ 2 + n ^ 2)) * n ≤ r
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have hp : r ^ 3 ≤ n ^ 3 := pow_le_pow_left₀ hr.le hfar 3
  have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg hr.le hn.le)
  nlinarith [mul_nonneg (mul_nonneg hr.le (sq_nonneg n)) (sq_nonneg (r ^ 2))]

theorem norm_regularizedLogGradient_zero_sub_square_le
    {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    ‖regularizedLogGradient x 0 y - regularizedLogGradient x (r ^ 2) y‖ ≤
      2 * truncInvNorm r (y - x) + r := by
  by_cases hnear : ‖y - x‖ < r
  · rw [truncInvNorm, if_pos hnear]
    exact ((norm_sub_le _ _).trans (add_le_add
      (norm_regularizedLogGradient_le x 0 y)
      (norm_regularizedLogGradient_le x (r ^ 2) y))).trans (by linarith)
  · exact (norm_regularizedLogGradient_zero_sub_square_far_le hr x y (not_lt.mp hnear)).trans
      (by linarith [truncInvNorm_nonneg r (y - x)])

theorem norm_integral_regularizedLogGradient_error_le
    {f : ℂ → ℝ} {M r : ℝ} (hf : Integrable f) (hM : ∀ y, |f y| ≤ M)
    (hr : 0 < r) (x : ℂ) :
    ‖∫ y, (f y : ℂ) *
      (regularizedLogGradient x 0 y - regularizedLogGradient x (r ^ 2) y)‖ ≤
      4 * Real.pi * M * r + r * ∫ y, |f y| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let B : ℂ → ℝ := fun y => 2 * M * truncInvNorm r (y - x) + r * |f y|
  have hI : Integrable B :=
    (((integrable_truncInvNorm r).comp_sub_right x).const_mul (2 * M)).add (hf.abs.const_mul r)
  have hb (y : ℂ) : ‖(f y : ℂ) *
      (regularizedLogGradient x 0 y - regularizedLogGradient x (r ^ 2) y)‖ ≤ B y := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he := mul_le_mul_of_nonneg_left
      (norm_regularizedLogGradient_zero_sub_square_le hr x y) (abs_nonneg (f y))
    have hm := mul_le_mul_of_nonneg_right (hM y) (truncInvNorm_nonneg r (y - x))
    dsimp only [B]
    nlinarith
  apply (norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall hb)).trans_eq
  dsimp only [B]
  rw [integral_add (((integrable_truncInvNorm r).comp_sub_right x).const_mul (2 * M))
    (hf.abs.const_mul r), integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (fun z : ℂ => truncInvNorm r z), integral_truncInvNorm hr]
  ring

end Euler2D
