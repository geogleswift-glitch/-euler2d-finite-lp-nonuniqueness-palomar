module

public import Mathlib

/-! A true quadratic observable remainder transfers a full Banach
orbit asymptotic to its actual observable, with a quantitative error. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

namespace Euler2D

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem observable_quadratic_backward_asymptotic
    (φ : E → H) (D : E →L[ℝ] H) (x : ℕ → E) (c : E)
    {a b κ C B : ℝ} (hκ : 0 ≤ κ)
    (hnorm : ∀ n, ‖x n‖ ≤ C * b ^ n)
    (herror : ∀ n, ‖x n - (a⁻¹) ^ n • c‖ ≤ B * (b ^ 2) ^ n)
    (hquad : ∀ n, ‖φ (x n) - D (x n)‖ ≤ κ * ‖x n‖ ^ 2) (n : ℕ) :
    ‖φ (x n) - (a⁻¹) ^ n • D c‖ ≤ (κ * C ^ 2 + ‖D‖ * B) * (b ^ 2) ^ n := by
  have hid : φ (x n) - (a⁻¹) ^ n • D c =
      (φ (x n) - D (x n)) + D (x n - (a⁻¹) ^ n • c) := by
    rw [D.map_sub, D.map_smul]
    abel
  have hs : ‖x n‖ ^ 2 ≤ (C * b ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
  have hp : (b ^ n) ^ 2 = (b ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  rw [hid]
  calc
    _ ≤ ‖φ (x n) - D (x n)‖ + ‖D (x n - (a⁻¹) ^ n • c)‖ := norm_add_le _ _
    _ ≤ κ * ‖x n‖ ^ 2 + ‖D‖ * ‖x n - (a⁻¹) ^ n • c‖ :=
      add_le_add (hquad n) (D.le_opNorm _)
    _ ≤ κ * (C * b ^ n) ^ 2 + ‖D‖ * (B * (b ^ 2) ^ n) := add_le_add
      (mul_le_mul_of_nonneg_left hs hκ) (mul_le_mul_of_nonneg_left (herror n) (norm_nonneg D))
    _ = _ := by rw [mul_pow, hp]; ring

end Euler2D

end
