module

public import RequestProject.Euler.WeightedCurrentOuterRowBudget

/-! Exact current-target finite row algebra, including the periodic
self term. The cutoff and the ancestor maximum keep their original
indices: current k is not inserted into the maximum over Fin k. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open scoped BigOperators

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem current_prefix_planar_row_sum (O U b ρ : ℝ) (k : ℕ) (x : ℕ → E) :
    (∑ l : Fin (k + 1), if (l : ℕ) < k then
      O * b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖
      else if k < (l : ℕ) then
      U * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - k)) * ‖x l‖ else 0) =
    O * (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hterm (l : Fin k) :
      (if (l.castSucc : ℕ) < k then
        O * b ^ (k - (l.castSucc : ℕ)) * ρ ^ (2 * (k - (l.castSucc : ℕ))) * ‖x l.castSucc‖
        else if k < (l.castSucc : ℕ) then
        U * b ^ (k - (l.castSucc : ℕ)) * ρ ^ (6 * ((l.castSucc : ℕ) - k)) * ‖x l.castSucc‖ else 0) =
      O * (b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) := by
    simp only [Fin.val_castSucc]
    rw [if_pos l.isLt]
    ring
  simp_rw [hterm]
  simp only [Fin.val_last, lt_self_iff_false, if_false, add_zero, Finset.mul_sum]

theorem current_prefix_torus_row_sum (V B b ρ : ℝ) (k : ℕ) (x : ℕ → E) :
    (∑ l : Fin (k + 1), if k ≤ (l : ℕ) then
      V * B * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - k)) * ‖x l‖
      else V * B * b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) =
    (V * B) * (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) +
      V * B * ‖x k‖ := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hterm (l : Fin k) :
      (if k ≤ (l.castSucc : ℕ) then
        V * B * b ^ (k - (l.castSucc : ℕ)) * ρ ^ (6 * ((l.castSucc : ℕ) - k)) * ‖x l.castSucc‖
        else V * B * b ^ (k - (l.castSucc : ℕ)) * ρ ^ (2 * (k - (l.castSucc : ℕ))) * ‖x l.castSucc‖) =
      (V * B) * (b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) := by
    simp only [Fin.val_castSucc]
    rw [if_neg (Nat.not_le_of_lt l.isLt)]
    ring
  simp_rw [hterm]
  simp only [Fin.val_last, le_refl, if_true, Nat.sub_self, Nat.mul_zero, pow_zero,
    mul_one, Finset.mul_sum]

theorem current_prefix_rows_le_polynomial_margin {O U V B b ρ C₀ K Δ t : ℝ}
    (hO : 0 ≤ O) (hV : 0 ≤ V) (hB : B ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 ≤ 1 / 2) (hK : 0 ≤ K) (hΔ : 0 ≤ Δ)
    (k : ℕ) (x : ℕ → E) (hx : weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K)
    (hsmall : (2 * b * C₀ * K * (O + V)) * ρ ^ 2 ≤ Δ) (ht : 0 ≤ t) :
    (∑ l : Fin (k + 1), if (l : ℕ) < k then
      O * b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖
      else if k < (l : ℕ) then
      U * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - k)) * ‖x l‖ else 0) +
    (∑ l : Fin (k + 1), if k ≤ (l : ℕ) then
      V * B * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - k)) * ‖x l‖
      else V * B * b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) ≤
      V * B * ‖x k‖ + Δ * ρ ^ 6 * (1 + t) ^ 4 := by
  rw [current_prefix_planar_row_sum, current_prefix_torus_row_sum]
  have hsum : 0 ≤ ∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hVB : V * B ≤ V := mul_le_of_le_one_right hV hB
  have hforce := weighted_current_outer_forcing_le_rhoSix_budget hb hb1 hC₀ hρ hζ hK
    (add_nonneg hO hV) hΔ k x hx hsmall ht
  nlinarith only [mul_le_mul_of_nonneg_right hVB hsum, hforce]

end Euler2D

end
