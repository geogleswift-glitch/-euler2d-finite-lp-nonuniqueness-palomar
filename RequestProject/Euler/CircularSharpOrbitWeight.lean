module

public import RequestProject.Euler.CircularHyperbolicGap

/-! A concrete true decay weight strong enough for a summable
quadratic remainder after unstable normalization. -/

@[expose] public section

noncomputable section

namespace Euler2D

def circularAncientBackwardWeight : ℝ := lamMult ^ 2 / 2
def circularAncientBackwardRatio : ℝ := 2 / lamMult ^ 2

theorem four_lt_lamMult_sq : (4 : ℝ) < lamMult ^ 2 := by nlinarith [two_lt_lamMult]

theorem circularAncientBackwardWeight_bounds :
    2 < circularAncientBackwardWeight ∧ circularAncientBackwardWeight < lamMult ^ 2 := by
  unfold circularAncientBackwardWeight
  constructor <;> nlinarith [four_lt_lamMult_sq]

theorem circularAncientBackwardWeight_inv :
    circularAncientBackwardWeight⁻¹ = circularAncientBackwardRatio := by
  unfold circularAncientBackwardWeight circularAncientBackwardRatio
  rw [inv_div]

theorem circularAncientBackwardRatio_bounds :
    0 < circularAncientBackwardRatio ∧ circularAncientBackwardRatio < 1 / 2 := by
  have ha : 0 < lamMult ^ 2 := lt_trans (by norm_num) four_lt_lamMult_sq
  constructor
  · exact div_pos (by norm_num) ha
  · unfold circularAncientBackwardRatio
    apply (div_lt_iff₀ ha).mpr
    nlinarith [four_lt_lamMult_sq]

theorem circularAncientBackwardRatio_unstable_quadratic_gap :
    lamMult ^ 2 * circularAncientBackwardRatio ^ 2 < 1 := by
  have ha : 0 < lamMult ^ 2 := lt_trans (by norm_num) four_lt_lamMult_sq
  have he : lamMult ^ 2 * circularAncientBackwardRatio ^ 2 = 4 / lamMult ^ 2 := by
    unfold circularAncientBackwardRatio
    field_simp
    ring
  rw [he]
  exact (div_lt_one ha).mpr four_lt_lamMult_sq

theorem circularAncientBackwardRatio_stable_gaps :
    2 * circularAncientBackwardRatio < 1 ∧ 2 * circularAncientBackwardRatio ^ 2 < 1 := by
  have hb := circularAncientBackwardRatio_bounds
  constructor
  · linarith
  · nlinarith

end Euler2D

end
