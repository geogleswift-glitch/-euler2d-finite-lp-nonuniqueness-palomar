module

public import RequestProject.Euler.CircularActualCompleteProjectedForcing

/-! The complete physical source error and the actual quadratic
nonlinear remainder have a common rho^8 bound on the child clock.
The constants are independent of the cutoff and physical scales. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

namespace Euler2D

theorem material_transfer_error_le_rhoEight
    {Cs Cn b K ρ D η ε q : ℝ}
    (hCs : 0 ≤ Cs) (hCn : 0 ≤ Cn) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hε : ε ≤ K * ρ ^ 6) (hq0 : 0 ≤ q) (hq : q ≤ K * ρ ^ 6) :
    Cs * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε +
        ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η + ρ ^ 14 * (1 + D) ^ 4) +
      b * Cn * q ^ 2 ≤
    (Cs * (3 + K) + b * Cn * K ^ 2) *
      (ρ ^ 8 * (1 + D) ^ 8 + ρ ^ 6 * η) := by
  let V := ρ ^ 8 * (1 + D) ^ 8
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hD1 : 1 ≤ 1 + D := by linarith only [hD]
  have hD4 : (1 + D) ^ 4 ≤ (1 + D) ^ 8 := pow_le_pow_right₀ hD1 (by norm_num)
  have hP : 1 ≤ (1 + D) ^ 8 := one_le_pow₀ hD1
  have h10 : ρ ^ 10 ≤ ρ ^ 8 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  have h12 : ρ ^ 12 ≤ ρ ^ 8 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  have h14 : ρ ^ 14 ≤ ρ ^ 8 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  have h10V : ρ ^ 10 * (1 + D) ^ 8 ≤ V :=
    mul_le_mul_of_nonneg_right h10 (by positivity)
  have h8V : ρ ^ 8 * (1 + D) ^ 4 ≤ V :=
    mul_le_mul_of_nonneg_left hD4 (by positivity)
  have h14V : ρ ^ 14 * (1 + D) ^ 4 ≤ V := by
    calc
      _ ≤ ρ ^ 8 * (1 + D) ^ 4 := mul_le_mul_of_nonneg_right h14 (by positivity)
      _ ≤ V := h8V
  have heV : ρ ^ 6 * (1 + D) ^ 4 * ε ≤ K * V := by
    calc
      _ ≤ ρ ^ 6 * (1 + D) ^ 4 * (K * ρ ^ 6) :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      _ = K * (ρ ^ 12 * (1 + D) ^ 4) := by ring
      _ ≤ K * (ρ ^ 8 * (1 + D) ^ 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h12 (by positivity)) hK
      _ ≤ K * V := mul_le_mul_of_nonneg_left h8V hK
  have hqV : q ^ 2 ≤ K ^ 2 * V := by
    calc
      _ ≤ (K * ρ ^ 6) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = K ^ 2 * ρ ^ 12 := by ring
      _ ≤ K ^ 2 * ρ ^ 8 := mul_le_mul_of_nonneg_left h12 (sq_nonneg _)
      _ ≤ K ^ 2 * V := by
        dsimp only [V]
        calc
          _ = K ^ 2 * (ρ ^ 8 * 1) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hP (by positivity)) (sq_nonneg _)
  have hsource : ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε +
      ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η + ρ ^ 14 * (1 + D) ^ 4 ≤
      (3 + K) * V + ρ ^ 6 * η := by linarith only [h10V, heV, h8V, h14V]
  calc
    _ ≤ Cs * ((3 + K) * V + ρ ^ 6 * η) + b * Cn * (K ^ 2 * V) :=
      add_le_add (mul_le_mul_of_nonneg_left hsource hCs)
        (mul_le_mul_of_nonneg_left hqV (mul_nonneg hb hCn))
    _ = (Cs * (3 + K) + b * Cn * K ^ 2) * V + Cs * (ρ ^ 6 * η) := by ring
    _ ≤ (Cs * (3 + K) + b * Cn * K ^ 2) * V +
        (Cs * (3 + K) + b * Cn * K ^ 2) * (ρ ^ 6 * η) := by
      have hcoef : Cs ≤ Cs * (3 + K) + b * Cn * K ^ 2 := by
        nlinarith only [hCs, mul_nonneg hCs hK,
          mul_nonneg (mul_nonneg hb hCn) (sq_nonneg K)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (by positivity))
    _ = _ := by dsimp only [V]; ring

end Euler2D

end
