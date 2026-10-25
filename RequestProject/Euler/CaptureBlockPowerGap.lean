module

public import Mathlib

@[expose] public section

noncomputable section

namespace Euler2D

theorem exists_capture_block_power_gap {lam C : ℝ} (hlam : 2 < lam) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ C * 2 ^ k ≤ q ∧ q ^ 2 < (lam ^ 2) ^ k := by
  let θ : ℝ := (lam + 2) / 2
  have hθ : 2 < θ := by dsimp only [θ]; linarith
  have hθlam : θ < lam := by dsimp only [θ]; linarith
  have hratio : 1 < θ / 2 := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  let k := n + 1
  have hk : 0 < k := Nat.succ_pos n
  have hC : C ≤ (θ / 2) ^ k := hn.le.trans (pow_le_pow_right₀ hratio.le (Nat.le_succ n))
  refine ⟨k, hk, θ ^ k, one_lt_pow₀ (by linarith : 1 < θ) hk.ne', ?_, ?_⟩
  · calc
      C * 2 ^ k ≤ (θ / 2) ^ k * 2 ^ k := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = θ ^ k := by rw [← mul_pow]; congr 1; ring
  · have hh : θ ^ k < lam ^ k := pow_lt_pow_left₀ hθlam (by linarith) hk.ne'
    have he : (lam ^ k) ^ 2 = (lam ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [← he]
    exact pow_lt_pow_left₀ hh (pow_nonneg (by linarith) _) (by decide)

end Euler2D

end
