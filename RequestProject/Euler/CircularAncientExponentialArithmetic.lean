module

public import RequestProject.Euler.CircularSharpOrbitWeight

/-! The actual multiplier and the chosen sharp decay weight give
a strictly faster continuous-time error exponent. The true complex
Floquet factor is exactly the original growing exponential. -/

@[expose] public section

noncomputable section

open Complex

namespace Euler2D

theorem lamMult_sq_eq_exp_doublePeriod : lamMult ^ 2 = Real.exp (sigma * (period + period)) := by
  rw [lamMult, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem exp_lamStar_doublePeriod :
    Complex.exp (((period + period : ℝ) : ℂ) * lamStar) = ((lamMult ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, period_multipliers_m4.1]
  push_cast
  ring

theorem circularGrowing_exponential_cell (κ : ℂ) (n : ℕ) (s : ℝ) :
    ((lamMult ^ 2)⁻¹) ^ n • (κ * Complex.exp ((s : ℂ) * lamStar)) =
      κ * Complex.exp (((-(n : ℝ) * (period + period) + s : ℝ) : ℂ) * lamStar) := by
  have hexp : Complex.exp (((-(n : ℝ) * (period + period) : ℝ) : ℂ) * lamStar) =
      (((lamMult ^ 2)⁻¹) ^ n : ℝ) := by
    calc
      _ = Complex.exp ((n : ℂ) * -(((period + period : ℝ) : ℂ) * lamStar)) := by
        congr 1
        push_cast
        ring
      _ = (Complex.exp (-(((period + period : ℝ) : ℂ) * lamStar))) ^ n := Complex.exp_nat_mul _ n
      _ = _ := by rw [Complex.exp_neg, exp_lamStar_doublePeriod]; push_cast; rfl
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, hexp, Complex.real_smul]
  ring

theorem exists_circularAncient_faster_error_exponent :
    ∃ δ > 0, Real.exp (-(sigma + δ) * (period + period)) = circularAncientBackwardRatio ^ 2 := by
  have hD : 0 < period + period := by unfold period; positivity
  have ha : 0 < lamMult ^ 2 := by nlinarith [four_lt_lamMult_sq]
  have hb : 0 < circularAncientBackwardRatio ^ 2 := sq_pos_of_pos circularAncientBackwardRatio_bounds.1
  have hprod : 0 < lamMult ^ 2 * circularAncientBackwardRatio ^ 2 := mul_pos ha hb
  have hlog := Real.log_lt_log hprod circularAncientBackwardRatio_unstable_quadratic_gap
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb), Real.log_one,
    lamMult_sq_eq_exp_doublePeriod, Real.log_exp] at hlog
  let α := -Real.log (circularAncientBackwardRatio ^ 2) / (period + period)
  have hα : sigma < α := (lt_div_iff₀ hD).mpr (by linarith)
  refine ⟨α - sigma, sub_pos.mpr hα, ?_⟩
  have he : -(sigma + (α - sigma)) * (period + period) = Real.log (circularAncientBackwardRatio ^ 2) := by
    calc
      _ = (Real.log (circularAncientBackwardRatio ^ 2) / (period + period)) * (period + period) := by
        dsimp only [α]
        ring
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hD)
  rw [he, Real.exp_log hb]

end Euler2D

end
