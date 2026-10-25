module

public import RequestProject.Euler.CircularCaptureCascadeClockBudget

/-! The actual past forcing error is rho^8, while the retained response
has size rho^6. The remaining rho^2 absorbs the parent amplification
along the real logarithmic cascade clock, with a strict positive margin. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

open Filter Topology Polynomial

namespace Euler2D

theorem circularCapture_cascade_parent_amplification_margin {b L : ℝ}
    (hb : 0 < b) (hbquarter : b < 1 / 4) (hclock : sigma * L < 8) :
    (b * sigma) * L < 2 := by
  have hmul := mul_lt_mul_of_pos_left hclock hb
  have hsmall : b * 8 < 2 := by linarith only [hbquarter]
  calc
    _ = b * (sigma * L) := by ring
    _ < b * 8 := hmul
    _ < 2 := hsmall

theorem tendsto_circularCapture_normalized_past_remainder
    (K θ L D d : ℝ) (n : ℕ) (hmargin : θ * L < 2) :
    Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ 2 * (1 + L * ξ + D) ^ n *
      Real.exp (θ * (L * ξ + D + d))) atTop (𝓝 0) := by
  let p : ℝ[X] := Polynomial.C (K * Real.exp (θ * (D + d))) *
    (1 + (Polynomial.C L * X + Polynomial.C D)) ^ n
  have hrate : 0 < 2 - θ * L := sub_pos.mpr hmargin
  convert tendsto_polynomial_mul_exp_decay p hrate using 1
  ext ξ
  have hp : p.eval ξ = (K * Real.exp (θ * (D + d))) * (1 + L * ξ + D) ^ n := by
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
    ring
  have he : Real.exp (-ξ) ^ 2 * Real.exp (θ * (L * ξ + D + d)) =
      Real.exp (θ * (D + d)) * Real.exp (-(2 - θ * L) * ξ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num <;> ring
  rw [hp]
  calc
    _ = K * (1 + L * ξ + D) ^ n *
        (Real.exp (-ξ) ^ 2 * Real.exp (θ * (L * ξ + D + d))) := by ring
    _ = _ := by rw [he]; ring

theorem eventually_circularCapture_normalized_past_remainder_small
    {K θ L D d ε : ℝ} (hK : 0 ≤ K) (hθ : 0 ≤ θ) (hε : 0 < ε)
    (n : ℕ) (hmargin : θ * L < 2) :
    ∀ᶠ ξ : ℝ in atTop, ∀ exit : ℝ, 0 ≤ exit → exit ≤ L * ξ + D →
      K * Real.exp (-ξ) ^ 2 * (1 + exit) ^ n * Real.exp (θ * (exit + d)) ≤ ε := by
  have ht := tendsto_circularCapture_normalized_past_remainder K θ L D d n hmargin
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with ξ hξ
  intro exit hexit hclock
  have hupper : 0 ≤ 1 + L * ξ + D := by linarith only [hexit, hclock]
  have hpowers : (1 + exit) ^ n ≤ (1 + L * ξ + D) ^ n := by
    apply pow_le_pow_left₀ (by linarith only [hexit])
    linarith only [hclock]
  have hexp : Real.exp (θ * (exit + d)) ≤ Real.exp (θ * (L * ξ + D + d)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add hclock le_rfl) hθ)
  calc
    _ ≤ K * Real.exp (-ξ) ^ 2 * (1 + L * ξ + D) ^ n * Real.exp (θ * (exit + d)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowers (mul_nonneg hK (pow_nonneg (Real.exp_pos _).le 2)))
        (Real.exp_pos _).le
    _ ≤ _ := (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hξ.le

theorem eventually_circularCapture_actual_past_error_relative_small
    {C θ L D d ε : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hε : 0 < ε)
    (hmargin : θ * L < 2) :
    ∀ᶠ ξ : ℝ in atTop, ∀ exit Lback : ℝ,
      0 ≤ exit → exit ≤ L * ξ + D → 0 ≤ Lback → Lback ≤ exit →
      (C * Real.exp (-ξ) ^ 8) * (exit - Lback) * Real.exp (θ * (exit + d)) ≤
        ε * Real.exp (-ξ) ^ 6 := by
  filter_upwards [eventually_circularCapture_normalized_past_remainder_small
    (K := C) (θ := θ) (L := L) (D := D) (d := d) hC hθ hε 1 hmargin] with ξ hξ
  intro exit Lback hexit hclock hLback _
  have hsmall := hξ exit hexit hclock
  simp only [pow_one] at hsmall
  have hlinear : exit - Lback ≤ 1 + exit := by linarith only [hLback]
  calc
    _ ≤ (C * Real.exp (-ξ) ^ 8) * (1 + exit) * Real.exp (θ * (exit + d)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlinear (by positivity)) (Real.exp_pos _).le
    _ = (C * Real.exp (-ξ) ^ 2 * (1 + exit) * Real.exp (θ * (exit + d))) *
        Real.exp (-ξ) ^ 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

end Euler2D

end
