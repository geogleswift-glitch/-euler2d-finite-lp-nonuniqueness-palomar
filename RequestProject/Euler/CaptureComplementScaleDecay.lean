module

public import RequestProject.Euler.FiniteSharpCaptureComplement

/-! The true lower bound for a rho^6 seed and the finite terminal
amplitude bound turn slower complementary growth into a uniform rho^3
error. The estimate is uniform in the finite capture index and retains
the separate state-proportional forcing error. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

namespace Euler2D

theorem rho_six_complement_power_le_cube
    {ρ seed c D qbar lam : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c) (hqbar : 0 ≤ qbar)
    (hgap : qbar ^ 2 ≤ lam) (hseed : c * ρ ^ 6 ≤ seed) (n : ℕ)
    (hterminal : seed * lam ^ n ≤ D) :
    ρ ^ 6 * qbar ^ n ≤ (D / c + 1) * ρ ^ 3 := by
  have hlam : 0 ≤ lam := (sq_nonneg qbar).trans hgap
  have hseed0 : 0 ≤ seed := (mul_nonneg hc.le (pow_nonneg hρ 6)).trans hseed
  have hD : 0 ≤ D := (mul_nonneg hseed0 (pow_nonneg hlam n)).trans hterminal
  have hB : 0 ≤ D / c := div_nonneg hD hc.le
  have hlarge : D / c ≤ (D / c + 1) ^ 2 := by nlinarith only [hB, sq_nonneg (D / c)]
  have hpower : (qbar ^ n) ^ 2 ≤ lam ^ n := by
    calc
      (qbar ^ n) ^ 2 = (qbar ^ 2) ^ n := by simp only [← pow_mul, Nat.mul_comm]
      _ ≤ lam ^ n := pow_le_pow_left₀ (sq_nonneg qbar) hgap n
  have hscale : ρ ^ 6 * lam ^ n ≤ D / c := by
    apply (le_div_iff₀ hc).mpr
    have hh := (mul_le_mul_of_nonneg_right hseed (pow_nonneg hlam n)).trans hterminal
    nlinarith only [hh]
  have hsquare : (ρ ^ 6 * qbar ^ n) ^ 2 ≤ ((D / c + 1) * ρ ^ 3) ^ 2 := by
    calc
      (ρ ^ 6 * qbar ^ n) ^ 2 = ρ ^ 6 * (ρ ^ 6 * (qbar ^ n) ^ 2) := by ring
      _ ≤ ρ ^ 6 * (ρ ^ 6 * lam ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower (pow_nonneg hρ 6))
          (pow_nonneg hρ 6)
      _ ≤ ρ ^ 6 * (D / c) := mul_le_mul_of_nonneg_left hscale (pow_nonneg hρ 6)
      _ ≤ ρ ^ 6 * (D / c + 1) ^ 2 := mul_le_mul_of_nonneg_left hlarge (pow_nonneg hρ 6)
      _ = ((D / c + 1) * ρ ^ 3) ^ 2 := by ring
  exact (sq_le_sq₀ (mul_nonneg (pow_nonneg hρ 6) (pow_nonneg hqbar n))
    (mul_nonneg (by positivity) (pow_nonneg hρ 3))).mp hsquare

theorem sharp_capture_error_le_cube
    {ρ seed c D qbar lam κ A e : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c) (hqbar : 0 ≤ qbar)
    (hgap : qbar ^ 2 ≤ lam) (hqlam : qbar < lam) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hseed : c * ρ ^ 6 ≤ seed) (n : ℕ) (hterminal : seed * lam ^ n ≤ D)
    (he : e ≤ qbar ^ n * (A * ρ ^ 6) + κ * (3 * seed) * lam ^ n / (lam - qbar)) :
    e ≤ A * (D / c + 1) * ρ ^ 3 + 3 * κ * D / (lam - qbar) := by
  have hpow := rho_six_complement_power_le_cube hρ hc hqbar hgap hseed n hterminal
  have hfirst : qbar ^ n * (A * ρ ^ 6) ≤ A * (D / c + 1) * ρ ^ 3 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hpow hA
  have hsecond : κ * (3 * seed) * lam ^ n / (lam - qbar) ≤ 3 * κ * D / (lam - qbar) := by
    apply div_le_div_of_nonneg_right ?_ (sub_pos.mpr hqlam).le
    have hh := mul_le_mul_of_nonneg_left hterminal (show 0 ≤ 3 * κ by positivity)
    nlinarith only [hh]
  exact he.trans (add_le_add hfirst hsecond)

end Euler2D

end
