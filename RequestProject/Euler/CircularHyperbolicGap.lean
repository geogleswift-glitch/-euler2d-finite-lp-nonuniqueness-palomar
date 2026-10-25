module

public import RequestProject.Euler.NormalEigen

/-! Concrete strict growth gaps for the genuine double-period
unstable multiplier and the weighted backward-orbit construction. -/

@[expose] public section

noncomputable section

namespace Euler2D

theorem two_lt_lamMult : 2 < lamMult := by
  have hsqrt : (3 : ℝ) < Real.sqrt 15 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sqrt_nonneg (15 : ℝ)]
  have hs : (27 / 100 : ℝ) < sigma := by rw [sigma_eq']; nlinarith
  have hp : (12 : ℝ) < period := by unfold period; nlinarith [Real.pi_gt_three]
  have hsp : 1 < sigma * period := by nlinarith [sigma_pos]
  have he := Real.add_one_le_exp (sigma * period)
  unfold lamMult
  linarith

theorem three_lt_lamMult_sq : (3 : ℝ) < lamMult ^ 2 := by
  nlinarith [two_lt_lamMult]

theorem three_div_lamMult_sq_lt_one : (3 : ℝ) / lamMult ^ 2 < 1 :=
  (div_lt_one (by nlinarith [two_lt_lamMult] : 0 < lamMult ^ 2)).mpr three_lt_lamMult_sq

end Euler2D

end
