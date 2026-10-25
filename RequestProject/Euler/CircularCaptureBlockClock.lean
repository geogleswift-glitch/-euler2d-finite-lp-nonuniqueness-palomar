module

public import RequestProject.Euler.CircularAncientExponentialArithmetic

/-! The fixed even block retains the original physical clock and sigma.
The true block gap gives the same strictly greater than one-half capture
error exponent in physical time. -/

@[expose] public section

noncomputable section

namespace Euler2D

def circularCaptureBlockTime (k : ℕ) : ℝ := ((2 * k : ℕ) : ℝ) * period

def circularCaptureBlockMultiplier (k : ℕ) : ℝ := (lamMult ^ 2) ^ k

theorem circularCaptureBlockTime_pos {k : ℕ} (hk : 0 < k) : 0 < circularCaptureBlockTime k := by
  unfold circularCaptureBlockTime
  exact mul_pos (Nat.cast_pos.mpr (Nat.mul_pos (by decide) hk)) (by unfold period; positivity)

theorem circularCaptureBlockMultiplier_eq_exp (k : ℕ) :
    circularCaptureBlockMultiplier k = Real.exp (sigma * circularCaptureBlockTime k) := by
  unfold circularCaptureBlockMultiplier circularCaptureBlockTime
  rw [lamMult_sq_eq_exp_doublePeriod, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem circularCaptureBlock_clock_identity {k : ℕ} (hk : 0 < k) :
    circularCaptureBlockTime k / Real.log (circularCaptureBlockMultiplier k) = sigma⁻¹ := by
  rw [circularCaptureBlockMultiplier_eq_exp, Real.log_exp]
  have ht := (circularCaptureBlockTime_pos hk).ne'
  have hs := sigma_pos.ne'
  field_simp

theorem circularCaptureBlock_exit_exponent {k : ℕ} (hk : 0 < k) {q : ℝ}
    (hq : 1 < q) (hgap : q ^ 2 < circularCaptureBlockMultiplier k) :
    (1 / 2 : ℝ) < 1 - Real.log q / Real.log (circularCaptureBlockMultiplier k) := by
  have hlog : 0 < Real.log (circularCaptureBlockMultiplier k) := by
    rw [circularCaptureBlockMultiplier_eq_exp, Real.log_exp]
    exact mul_pos sigma_pos (circularCaptureBlockTime_pos hk)
  have hh := Real.log_lt_log (pow_pos (zero_lt_one.trans hq) 2) hgap
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hhalf : Real.log q / Real.log (circularCaptureBlockMultiplier k) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hlog).mpr
    nlinarith only [hh]
  linarith only [hhalf]

end Euler2D

end
