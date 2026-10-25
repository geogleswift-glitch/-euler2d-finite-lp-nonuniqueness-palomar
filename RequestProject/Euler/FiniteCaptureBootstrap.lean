module

public import RequestProject.Euler.FiniteWeightedCaptureRecurrence
public import RequestProject.Euler.CaptureWeightedSourceBudget

/-! Capture envelopes on an already existing finite recurrence.
The local one-step estimates are required only on the bootstrap ball;
the proof establishes that ball condition before each use. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open scoped BigOperators

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

theorem finite_capture_bootstrap
    (v : ℕ → E) (w : ℕ → F) (f : ℕ → ℝ)
    {lam q C κ D : ℝ} (hLam : 1 < lam) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (ha : 0 < ‖v 0‖) {N : ℕ}
    (hterminal : ‖v 0‖ * lam ^ N ≤ D)
    (hcomp : q + 3 * C * D ≤ lam)
    (hsmall : 9 * C * D / (lam - 1) + 3 * κ * (N : ℝ) ≤ 1 / 16)
    (hw0 : ‖w 0‖ ≤ ‖v 0‖ / 32)
    (hf : ∀ n ≤ N, ∑ j ∈ Finset.range n, f j / lam ^ (j + 1) ≤ ‖v 0‖ / 32)
    (hstep : ∀ n < N, ‖v n‖ + ‖w n‖ ≤ 3 * D →
      ‖v (n + 1) - lam • v n‖ ≤
        C * (‖v n‖ + ‖w n‖) ^ 2 + f n + κ * (‖v n‖ + ‖w n‖) ∧
      ‖w (n + 1)‖ ≤ q * ‖w n‖ +
        C * (‖v n‖ + ‖w n‖) * ‖w n‖ + f n + κ * (‖v n‖ + ‖w n‖)) :
    ∀ n ≤ N, (3 / 4 : ℝ) * ‖v 0‖ * lam ^ n ≤ ‖v n‖ ∧
      ‖v n‖ ≤ (5 / 4 : ℝ) * ‖v 0‖ * lam ^ n ∧
      ‖w n‖ ≤ (1 / 8 : ℝ) * ‖v 0‖ * lam ^ n := by
  have hl0 : 0 < lam := zero_lt_one.trans hLam
  have hp : 0 < lam - 1 := sub_pos.mpr hLam
  have hD : 0 ≤ D := (mul_nonneg ha.le (pow_nonneg hl0.le _)).trans hterminal
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      simp only [pow_zero, mul_one]
      constructor
      · nlinarith only [ha]
      constructor
      · nlinarith only [ha]
      · nlinarith only [ha, hw0]
    let b : ℕ → ℝ := fun j => ‖v j‖ + ‖w j‖
    have hb0 (j : ℕ) (_ : j < n) : 0 ≤ b j := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hb (j : ℕ) (hj : j < n) : b j ≤ 3 * ‖v 0‖ * lam ^ j := by
      obtain ⟨_, hv, hw⟩ := ih j hj (hj.le.trans hn)
      dsimp only [b]
      have hpos : 0 ≤ ‖v 0‖ * lam ^ j := mul_nonneg ha.le (pow_nonneg hl0.le j)
      nlinarith only [hv, hw, hpos]
    have hbn (j : ℕ) (hj : j < n) : b j ≤ 3 * D := by
      have he : ‖v 0‖ * lam ^ j ≤ D :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLam.le (hj.le.trans hn)) ha.le).trans hterminal
      exact (hb j hj).trans (by nlinarith only [he])
    have hterm : ‖v 0‖ * lam ^ n ≤ D :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLam.le hn) ha.le).trans hterminal
    have hκn : 3 * κ * (n : ℝ) ≤ 3 * κ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) (by positivity)
    have hsmalln : 9 * C * D / (lam - 1) + 3 * κ * (n : ℝ) ≤ 1 / 16 := by
      linarith only [hsmall, hκn]
    have hquad0 : 0 ≤ 9 * C * D / (lam - 1) := by positivity
    have hpro : 3 * κ * (n : ℝ) ≤ 1 / 16 := by linarith only [hsmalln, hquad0]
    have hbudget := capture_weighted_nonlinear_forcing_budget hLam (by norm_num : (0 : ℝ) ≤ 3)
      ha.le hC hκ hb0 hb hterm (hf n hn)
    have hbudgetA :
        (∑ j ∈ Finset.range n, (C * (b j) ^ 2 + f j + κ * b j) / lam ^ (j + 1)) ≤
          (1 / 8 : ℝ) * ‖v 0‖ := by
      have he : C * (3 ^ 2 * ‖v 0‖ * D / (lam - 1)) + ‖v 0‖ / 32 +
          κ * ((n : ℝ) * 3 * ‖v 0‖) =
          ‖v 0‖ * (9 * C * D / (lam - 1) + 3 * κ * (n : ℝ) + 1 / 32) := by ring
      rw [he] at hbudget
      nlinarith only [hbudget, mul_le_mul_of_nonneg_left hsmalln ha.le, ha]
    have hdef : (∑ j ∈ Finset.range n, ‖v (j + 1) - lam • v j‖ / lam ^ (j + 1)) ≤
        (1 / 8 : ℝ) * ‖v 0‖ := by
      apply le_trans (Finset.sum_le_sum ?_) hbudgetA
      intro j hj
      have hjn := Finset.mem_range.mp hj
      exact div_le_div_of_nonneg_right (hstep j (hjn.trans_le hn) (hbn j hjn)).1
        (pow_nonneg hl0.le _)
    have hvenv := finite_amplitude_envelope_of_weighted_defect v hl0 hdef
    have hbudgetW := capture_weighted_nonlinear_forcing_budget hLam (by norm_num : (0 : ℝ) ≤ 3)
      ha.le (by norm_num : (0 : ℝ) ≤ 0) hκ hb0 hb hterm (hf n hn)
    have hsourceW :
        (∑ j ∈ Finset.range n, (f j + κ * b j) / lam ^ (j + 1)) ≤
          ‖v 0‖ / 32 + κ * ((n : ℝ) * 3 * ‖v 0‖) := by
      simpa only [zero_mul, zero_add] using hbudgetW
    have hwstep : ∀ j < n, ‖w (j + 1)‖ ≤ lam * ‖w j‖ + (f j + κ * b j) := by
      intro j hj
      have hbD := hbn j hj
      have hh := (hstep j (hj.trans_le hn) hbD).2
      have hcoef : q + C * b j ≤ lam := by
        have hm := mul_le_mul_of_nonneg_left hbD hC
        nlinarith only [hm, hcomp]
      have hc := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (w j))
      nlinarith only [hh, hc]
    have hwb := finite_weighted_recurrence_bound (u := fun j => ‖w j‖)
      (e := fun j => f j + κ * b j) hl0 hwstep n le_rfl
    have hwfinal : ‖w n‖ ≤ (1 / 8 : ℝ) * ‖v 0‖ * lam ^ n := by
      have hs : ‖w 0‖ + (∑ j ∈ Finset.range n, (f j + κ * b j) / lam ^ (j + 1)) ≤
          (1 / 8 : ℝ) * ‖v 0‖ := by
        nlinarith only [hw0, hsourceW, mul_le_mul_of_nonneg_left hpro ha.le]
      exact hwb.trans ((mul_le_mul_of_nonneg_left hs (pow_nonneg hl0.le n)).trans_eq (mul_comm _ _))
    have hpos : 0 ≤ ‖v 0‖ * lam ^ n := mul_nonneg ha.le (pow_nonneg hl0.le n)
    exact ⟨by nlinarith only [hvenv.1, hpos], by nlinarith only [hvenv.2, hpos], hwfinal⟩

end Euler2D

end
