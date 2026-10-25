module

public import Mathlib

/-! The actual delayed-response Gronwall factor is compatible with
rho-six capture on a logarithmic cumulative horizon. All polynomial
losses in that horizon are retained. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Filter Topology Polynomial

namespace Euler2D

theorem tendsto_polynomial_mul_exp_decay (p : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => p.eval x * Real.exp (-a * x)) atTop (𝓝 0) := by
  have hh := ((p.comp (C a⁻¹ * X)).tendsto_div_exp_atTop).comp
    (show Tendsto (fun x : ℝ => a * x) atTop atTop from tendsto_id.const_mul_atTop ha)
  convert hh using 1
  · ext x
    simp only [Function.comp_apply, eval_comp, eval_mul, eval_C, eval_X,
      inv_mul_cancel_left₀ ha.ne', div_eq_mul_inv, ← Real.exp_neg, neg_mul]

def retardedLogHorizon (b L C x : ℝ) : ℝ := (L * x + C) / (1 - b)

theorem tendsto_retardedResponse_geometric_polynomial (b K L C : ℝ) (n : ℕ)
    (hgap : K * b * L / (1 - b) < 2) :
    Tendsto (fun x : ℝ =>
      (Real.exp (-x)) ^ 2 *
        (b * retardedLogHorizon b L C x *
          Real.exp (K * b * retardedLogHorizon b L C x)) *
        (1 + retardedLogHorizon b L C x) ^ n /
          (1 - b * (Real.exp (-x)) ^ 2)) atTop (𝓝 0) := by
  let Y : ℝ[X] := Polynomial.C (L / (1 - b)) * X + Polynomial.C (C / (1 - b))
  let p : ℝ[X] := Polynomial.C b * Y * (1 + Y) ^ n
  have hY (x : ℝ) : Y.eval x = retardedLogHorizon b L C x := by
    simp only [Y, eval_add, eval_mul, eval_C, eval_X, retardedLogHorizon, div_eq_mul_inv]
    ring
  have hp (x : ℝ) : p.eval x = b * retardedLogHorizon b L C x *
      (1 + retardedLogHorizon b L C x) ^ n := by
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_one, hY]
  have hh := (tendsto_polynomial_mul_exp_decay p (sub_pos.mpr hgap)).const_mul
    (Real.exp (K * b * C / (1 - b)))
  have hden : Tendsto (fun x : ℝ => 1 - b * (Real.exp (-x)) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul b)
  have hmain := hh.div hden (by norm_num : (1 : ℝ) ≠ 0)
  convert hmain using 1
  · ext x
    have hex : Real.exp (-x) ^ 2 * Real.exp (K * b * retardedLogHorizon b L C x) =
        Real.exp (K * b * C / (1 - b)) *
          Real.exp (-(2 - K * b * L / (1 - b)) * x) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold retardedLogHorizon
      ring
    change _ = (Real.exp (K * b * C / (1 - b)) *
      (p.eval x * Real.exp (-(2 - K * b * L / (1 - b)) * x))) /
        (1 - b * Real.exp (-x) ^ 2)
    rw [hp]
    have hnum : Real.exp (-x) ^ 2 *
        (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
          (1 + retardedLogHorizon b L C x) ^ n =
        Real.exp (K * b * C / (1 - b)) *
          (b * retardedLogHorizon b L C x * (1 + retardedLogHorizon b L C x) ^ n *
            Real.exp (-(2 - K * b * L / (1 - b)) * x)) := by
      calc
        _ = (b * retardedLogHorizon b L C x * (1 + retardedLogHorizon b L C x) ^ n) *
          (Real.exp (-x) ^ 2 * Real.exp (K * b * retardedLogHorizon b L C x)) := by ring
        _ = _ := by rw [hex]; ring
    exact congrArg (fun z : ℝ => z / (1 - b * Real.exp (-x) ^ 2)) hnum
  · simp

theorem eventually_retardedResponse_absorption (b K L C feedback : ℝ)
    (hgap : K * b * L / (1 - b) < 2) :
    ∀ᶠ x : ℝ in atTop,
      2 * (b * retardedLogHorizon b L C x * Real.exp (K * b * retardedLogHorizon b L C x)) *
        (feedback * b * (Real.exp (-x)) ^ 2 / (1 - b * (Real.exp (-x)) ^ 2)) ≤ 1 := by
  have hh := (tendsto_retardedResponse_geometric_polynomial b K L C 0 hgap).const_mul
    (2 * feedback * b)
  simp only [mul_zero] at hh
  have he := hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he] with x hx
  simp only [pow_zero, mul_one, mul_zero] at hx
  convert hx.le using 1 <;> ring

end Euler2D

end
