module

public import RequestProject.Euler.CircularCaptureBlockClock
public import RequestProject.Euler.CaptureFiniteHorizon

/-! The actual fixed even return block has the original six-over-sigma
capture clock for every positive rho-six seed coefficient. That fixed
coefficient, which may depend on the chosen nonzero transfer ratio,
is retained in the additive time constant. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

namespace Euler2D

theorem exists_circularCapture_rhoSix_horizon {k : ℕ} (hk : 0 < k)
    {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ a : ℝ}, 0 < ρ → ρ < 1 →
      0 < a → a < δ → H * ρ ^ 6 ≤ a →
      ∃ N : ℕ, 0 < N ∧
        δ < (3 / 4 : ℝ) * a * circularCaptureBlockMultiplier k ^ N ∧
        a * circularCaptureBlockMultiplier k ^ N ≤
          (4 / 3 : ℝ) * circularCaptureBlockMultiplier k * δ ∧
        (N : ℝ) * circularCaptureBlockTime k ≤
          (6 / sigma) * Real.log (1 / ρ) + C := by
  let T := circularCaptureBlockTime k
  let lam := circularCaptureBlockMultiplier k
  have hT : 0 < T := circularCaptureBlockTime_pos hk
  have hσ : 0 < sigma := sigma_pos
  have hlam : 1 < lam := by
    change 1 < circularCaptureBlockMultiplier k
    rw [circularCaptureBlockMultiplier_eq_exp]
    exact Real.one_lt_exp_iff.mpr (mul_pos hσ hT)
  have hclock : T / Real.log lam = sigma⁻¹ := circularCaptureBlock_clock_identity hk
  let A : ℝ := Real.log ((4 / 3 : ℝ) * δ / H) / sigma
  let C : ℝ := |A| + T + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ρ a hρ _hρ1 ha haδ hseed
  obtain ⟨N, hN, hexit, hterminal, hn⟩ := exists_capture_finite_horizon hlam ha haδ
  refine ⟨N, hN, hexit, hterminal, ?_⟩
  have hratio : (4 / 3 : ℝ) * δ / a ≤ (4 / 3 : ℝ) * δ / (H * ρ ^ 6) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hseed
  have hlog := Real.log_le_log (by positivity : 0 < (4 / 3 : ℝ) * δ / a) hratio
  have hlogeq : Real.log ((4 / 3 : ℝ) * δ / (H * ρ ^ 6)) =
      Real.log ((4 / 3 : ℝ) * δ / H) + 6 * Real.log (1 / ρ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hH.ne' (by positivity),
      Real.log_pow, one_div, Real.log_inv, Real.log_div (by positivity) hH.ne']
    norm_num
    ring
  have hnT := mul_le_mul_of_nonneg_right hn hT.le
  have heq : (Real.log ((4 / 3 : ℝ) * δ / a) / Real.log lam + 1) * T =
      Real.log ((4 / 3 : ℝ) * δ / a) / sigma + T := by
    calc
      _ = Real.log ((4 / 3 : ℝ) * δ / a) * (T / Real.log lam) + T := by ring
      _ = _ := by rw [hclock]; ring
  rw [heq] at hnT
  have hh := div_le_div_of_nonneg_right hlog hσ.le
  rw [hlogeq] at hh
  have hh' : Real.log ((4 / 3 : ℝ) * δ / a) / sigma ≤
      A + (6 / sigma) * Real.log (1 / ρ) := by
    convert hh using 1 <;> dsimp only [A] <;> ring
  change (N : ℝ) * T ≤ _
  calc
    _ ≤ Real.log ((4 / 3 : ℝ) * δ / a) / sigma + T := hnT
    _ ≤ A + (6 / sigma) * Real.log (1 / ρ) + T := add_le_add hh' le_rfl
    _ ≤ _ := by dsimp only [C]; linarith only [le_abs_self A]

end Euler2D

end
