module

public import RequestProject.Euler.CircularCaptureBlockClock

/-! The real entrance amplitude selects its own first geometric
capture count. A rho^6 lower seed bounds its clock by 6/sigma times
the logarithmic scale, uniformly in the actual entrance amplitude. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Euler2D

theorem exists_parentCapture_first_crossing_logarithmic_count
    {ℓ : ℕ} (hℓ : 0 < ℓ) {δ cs : ℝ} (hδ : 0 < δ) (hcs : 0 < cs) :
    ∃ D₀ > 0, ∀ ξ a : ℝ,
      0 < a → cs * Real.exp (-ξ) ^ 6 ≤ a → a < δ →
      ∃ Ncap : ℕ, 0 < Ncap ∧
        δ ≤ (3 / 4 : ℝ) * a * circularCaptureBlockMultiplier ℓ ^ Ncap ∧
        a * circularCaptureBlockMultiplier ℓ ^ Ncap <
          (4 * circularCaptureBlockMultiplier ℓ / 3) * δ ∧
        (Ncap : ℝ) * circularCaptureBlockTime ℓ ≤ (6 / sigma) * ξ + D₀ := by
  let Tblock := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  let target := (4 / 3 : ℝ) * δ
  let gap := Real.log target - Real.log cs
  let D₀ := 1 + Tblock + |gap| / sigma
  have hTblock : 0 < Tblock := circularCaptureBlockTime_pos hℓ
  have htarget : 0 < target := mul_pos (by norm_num) hδ
  have hlamExp : lam = Real.exp (sigma * Tblock) := circularCaptureBlockMultiplier_eq_exp ℓ
  have hlam : 1 < lam := by rw [hlamExp]; exact Real.one_lt_exp_iff.mpr (mul_pos sigma_pos hTblock)
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hD₀ : 0 < D₀ := by
    dsimp only [D₀]
    exact add_pos_of_pos_of_nonneg (add_pos zero_lt_one hTblock)
      (div_nonneg (abs_nonneg _) sigma_pos.le)
  refine ⟨D₀, hD₀, ?_⟩
  intro ξ a ha hseed haδ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (target / a) hlam
  have hex : ∃ n : ℕ, target ≤ a * lam ^ n := by
    refine ⟨m, ?_⟩
    have hh := (div_lt_iff₀ ha).mp hm
    exact (by simpa only [mul_comm] using hh : target < a * lam ^ m).le
  let N := Nat.find hex
  have hcross : target ≤ a * lam ^ N := Nat.find_spec hex
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, pow_zero, mul_one] at hcross
    dsimp only [target] at hcross
    nlinarith only [hcross, haδ, hδ]
  have hpred : target > a * lam ^ (N - 1) := by
    apply lt_of_not_ge
    exact Nat.find_min hex (Nat.sub_lt hN (by decide : 0 < 1))
  have hstep : a * lam ^ N = lam * (a * lam ^ (N - 1)) := by
    calc
      _ = a * lam ^ ((N - 1) + 1) := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hN)]
      _ = _ := by rw [pow_succ]; ring
  have hterminal : a * lam ^ N < (4 * lam / 3) * δ := by
    rw [hstep]
    have hh := mul_lt_mul_of_pos_left hpred hlam0
    convert hh using 1 <;> dsimp only [target] <;> ring
  have hsmallPast : cs * Real.exp (-ξ) ^ 6 * lam ^ (N - 1) < target :=
    (mul_le_mul_of_nonneg_right hseed (pow_nonneg hlam0.le _)).trans_lt hpred
  have hexp : cs * Real.exp (-ξ) ^ 6 * lam ^ (N - 1) =
      Real.exp (Real.log cs - 6 * ξ + sigma * ((N - 1 : ℕ) : ℝ) * Tblock) := by
    calc
      _ = Real.exp (Real.log cs) * Real.exp (-ξ) ^ 6 *
          Real.exp (sigma * Tblock) ^ (N - 1) := by rw [Real.exp_log hcs, ← hlamExp]
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  rw [hexp] at hsmallPast
  have harg : Real.log cs - 6 * ξ + sigma * ((N - 1 : ℕ) : ℝ) * Tblock < Real.log target := by
    apply Real.exp_lt_exp.mp
    simpa only [Real.exp_log htarget] using hsmallPast
  have hNreal : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  have hclock : sigma * ((N : ℝ) * Tblock) =
      sigma * (((N - 1 : ℕ) : ℝ) * Tblock) + sigma * Tblock := by
    calc
      _ = sigma * ((((N - 1 : ℕ) : ℝ) + 1) * Tblock) := by rw [hNreal]
      _ = _ := by ring
  have hD₀eq : sigma * D₀ = sigma + sigma * Tblock + |gap| := by
    dsimp only [D₀]
    field_simp [sigma_pos.ne']
    <;> ring
  have hlogLe : Real.log target - Real.log cs ≤ |gap| := le_abs_self gap
  have hlogClock : (N : ℝ) * Tblock ≤ (6 / sigma) * ξ + D₀ := by
    have heq : (6 / sigma) * ξ + D₀ = (6 * ξ + sigma * D₀) / sigma := by
      field_simp [sigma_pos.ne']
      <;> ring
    rw [heq]
    apply (le_div_iff₀ sigma_pos).mpr
    nlinarith only [harg, hclock, hD₀eq, hlogLe, sigma_pos]
  refine ⟨N, hN, ?_, hterminal, hlogClock⟩
  dsimp only [target] at hcross
  nlinarith only [hcross]

end Euler2D

end
