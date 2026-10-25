module

public import RequestProject.Euler.CircularAmplitudeDoublePeriodEstimate

/-! A true full-time perturbation bound with geometric frequency
decay, for controlling powers of the actual monodromy in the high tail. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology NormedSpace

namespace Euler2D

theorem real_exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

theorem norm_circularAmplitude_exp_sub_uncoupled_le (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • circularAmplitudeGenerator N) - exp (t • circularUncoupledAmplitudeGenerator N)‖ ≤
      ((135 / 4 : ℝ) * t * cellA ^ N) * Real.exp ((45 / 4 : ℝ) * t * cellA ^ N) := by
  let b := circularAmplitudeCrossGenerator N
  have hb := norm_circularAmplitudeCrossGenerator_le N
  have h := norm_banachExponential_perturbation_le
    (circularUncoupledAmplitudeGenerator N) b (M := 3) (T := t) (by norm_num) ht
    (fun s _ => norm_exp_circularUncoupledAmplitudeGenerator_le N s)
    (fun s _ => norm_exp_circularUncoupledAmplitudeGenerator_le N (-s))
  rw [← circularAmplitudeGenerator_eq_uncoupled_add_cross] at h
  let x : ℝ := 9 * ‖b‖ * t
  let y : ℝ := (45 / 4 : ℝ) * t * cellA ^ N
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hy : 0 ≤ y := by
    have ha : 0 < cellA := cellA_pos
    dsimp only [y]
    positivity
  have hxy : x ≤ y := by
    calc
      _ ≤ 9 * ((5 / 4 : ℝ) * cellA ^ N) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) ht
      _ = _ := by dsimp only [y]; ring
  have hprod : x * Real.exp x ≤ y * Real.exp y :=
    mul_le_mul hxy (Real.exp_le_exp.mpr hxy) (Real.exp_pos x).le hy
  calc
    _ ≤ 3 * (Real.exp x - 1) := by simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using h
    _ ≤ 3 * (x * Real.exp x) := mul_le_mul_of_nonneg_left (real_exp_sub_one_le_mul_exp x) (by norm_num)
    _ ≤ 3 * (y * Real.exp y) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by dsimp only [y]; ring

end Euler2D

end
