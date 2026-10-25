module

public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! Cutoff-uniform bounds for the ACTUAL physical handoff clocks.
The only recurrence is a bound on consecutive physical capture times,
using the original ampScale. The strict b<1/4 margin also absorbs the
rho^8 whole-past forcing error after exponential history weighting. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Filter Topology Polynomial

namespace Euler2D

theorem finite_physicalCascade_clock_budget
    {A₀ b Ddeep Dstep : ℝ} (hA : 0 < A₀) (hb : 0 < b) (hb1 : b < 1)
    (hdeep : 0 ≤ Ddeep) (hstep : 0 ≤ Dstep)
    (N : ℕ) (times : ℕ → ℝ)
    (hfirst : ampScale A₀ b N * times N ≤ Ddeep)
    (hhandoff : ∀ k < N, times k ≤ times (k + 1) + Dstep / ampScale A₀ b k) :
    ∀ k ≤ N,
      ampScale A₀ b k * times k ≤ Ddeep + Dstep / (1 - b) ∧
      times k ≤ (Ddeep + Dstep / (1 - b)) / A₀ := by
  let C := Ddeep + Dstep / (1 - b)
  have hden : 0 < 1 - b := sub_pos.mpr hb1
  have hC : 0 ≤ C := add_nonneg hdeep (div_nonneg hstep hden.le)
  have hfirstC : Ddeep ≤ C := le_add_of_nonneg_right (div_nonneg hstep hden.le)
  have hidentity : (1 - b) * C = (1 - b) * Ddeep + Dstep := by
    dsimp only [C]
    field_simp [hden.ne'] <;> ring
  have hinvariant : b * C + Dstep ≤ C := by
    have hh := mul_nonneg hden.le hdeep
    nlinarith only [hidentity, hh]
  have hamp (k : ℕ) : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hscale (k : ℕ) : ampScale A₀ b k = b * ampScale A₀ b (k + 1) := by
    unfold ampScale
    rw [pow_succ]
    field_simp [hb.ne'] <;> ring
  have hbound : ∀ j : ℕ, ∀ k ≤ N, N - k = j → ampScale A₀ b k * times k ≤ C := by
    intro j
    induction j with
    | zero =>
      intro k hk hdiff
      have heq : k = N := by omega
      subst k
      exact hfirst.trans hfirstC
    | succ j ih =>
      intro k hk hdiff
      have hklt : k < N := by omega
      have hnext := ih (k + 1) (by omega) (by omega)
      have hcancel : ampScale A₀ b k * (Dstep / ampScale A₀ b k) = Dstep := by
        field_simp [(hamp k).ne']
      calc
        _ ≤ ampScale A₀ b k * (times (k + 1) + Dstep / ampScale A₀ b k) :=
          mul_le_mul_of_nonneg_left (hhandoff k hklt) (hamp k).le
        _ = b * (ampScale A₀ b (k + 1) * times (k + 1)) + Dstep := by
          rw [mul_add, hcancel, hscale]
          ring
        _ ≤ b * C + Dstep := add_le_add (mul_le_mul_of_nonneg_left hnext hb.le) le_rfl
        _ ≤ C := hinvariant
  intro k hk
  have hkbound := hbound (N - k) k hk rfl
  refine ⟨hkbound, ?_⟩
  have hAk : A₀ ≤ ampScale A₀ b k := by
    unfold ampScale
    apply (le_div_iff₀ (pow_pos hb k)).mpr
    exact mul_le_of_le_one_right hA.le (pow_le_one₀ hb.le hb1.le)
  exact ((le_div_iff₀ (hamp k)).mpr (by nlinarith only [hkbound])).trans
    (div_le_div_of_nonneg_left hC hA hAk)

theorem circularCapture_cascade_clock_log_margin {b : ℝ}
    (hb : 0 < b) (hbquarter : b < 1 / 4) :
    0 < (6 / sigma) / (1 - b) ∧ sigma * ((6 / sigma) / (1 - b)) < 8 := by
  have hden : 0 < 1 - b := by linarith only [hbquarter]
  refine ⟨div_pos (div_pos (by norm_num) sigma_pos) hden, ?_⟩
  have heq : sigma * ((6 / sigma) / (1 - b)) = 6 / (1 - b) := by
    field_simp [sigma_pos.ne', hden.ne']
  rw [heq]
  apply (div_lt_iff₀ hden).mpr
  linarith only [hbquarter]

theorem circularCapture_cascade_past_self_rate_margin {b K : ℝ}
    (hbquarter : b < 1 / 4) (hslow : b * K < sigma / 4) :
    K * ((6 / sigma) * b / (1 - b)) + 6 < 8 := by
  have hden : 0 < 1 - b := by linarith only [hbquarter]
  have hh : 0 < sigma * (1 / 4 - b) := mul_pos sigma_pos (sub_pos.mpr hbquarter)
  have hnum : 6 * (b * K) < 2 * (sigma * (1 - b)) := by
    nlinarith only [hslow, hh]
  have hfrac : 6 * (b * K) / (sigma * (1 - b)) < 2 :=
    (div_lt_iff₀ (mul_pos sigma_pos hden)).mpr hnum
  have heq : K * ((6 / sigma) * b / (1 - b)) = 6 * (b * K) / (sigma * (1 - b)) := by
    field_simp [sigma_pos.ne', hden.ne'] <;> ring
  rw [heq]
  linarith only [hfrac]

theorem tendsto_circularCapture_global_clock_remainder
    (K L D₀ : ℝ) (n : ℕ) (hmargin : sigma * L < 8) :
    Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ 8 * (1 + L * ξ + D₀) ^ n *
      Real.exp (sigma * (L * ξ + D₀))) atTop (𝓝 0) := by
  let p : ℝ[X] := Polynomial.C (K * Real.exp (sigma * D₀)) *
    (1 + (Polynomial.C L * X + Polynomial.C D₀)) ^ n
  have hrate : 0 < 8 - sigma * L := sub_pos.mpr hmargin
  convert tendsto_polynomial_mul_exp_decay p hrate using 1
  ext ξ
  have hp : p.eval ξ = (K * Real.exp (sigma * D₀)) * (1 + L * ξ + D₀) ^ n := by
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
    ring
  have he : Real.exp (-ξ) ^ 8 * Real.exp (sigma * (L * ξ + D₀)) =
      Real.exp (sigma * D₀) * Real.exp (-(8 - sigma * L) * ξ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num <;> ring
  rw [hp]
  calc
    _ = K * (1 + L * ξ + D₀) ^ n *
        (Real.exp (-ξ) ^ 8 * Real.exp (sigma * (L * ξ + D₀))) := by ring
    _ = _ := by rw [he]; ring

theorem eventually_circularCapture_global_clock_remainder_small
    {K L D₀ ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (n : ℕ)
    (hmargin : sigma * L < 8) :
    ∀ᶠ ξ : ℝ in atTop, ∀ exit : ℝ, 0 ≤ exit → exit ≤ L * ξ + D₀ →
      K * Real.exp (-ξ) ^ 8 * (1 + exit) ^ n * Real.exp (sigma * exit) ≤ ε := by
  have ht := tendsto_circularCapture_global_clock_remainder K L D₀ n hmargin
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with ξ hξ
  intro exit hexit hclock
  have hupper : 0 ≤ 1 + L * ξ + D₀ := by linarith only [hexit, hclock]
  have hpowers : (1 + exit) ^ n ≤ (1 + L * ξ + D₀) ^ n := by
    apply pow_le_pow_left₀ (by linarith only [hexit])
    linarith only [hclock]
  have hexp : Real.exp (sigma * exit) ≤ Real.exp (sigma * (L * ξ + D₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hclock sigma_pos.le)
  calc
    _ ≤ K * Real.exp (-ξ) ^ 8 * (1 + L * ξ + D₀) ^ n * Real.exp (sigma * exit) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowers (mul_nonneg hK (pow_nonneg (Real.exp_pos _).le 8)))
        (Real.exp_pos _).le
    _ ≤ _ := (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hξ.le

end Euler2D

end
