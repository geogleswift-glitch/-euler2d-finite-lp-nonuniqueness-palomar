module

public import RequestProject.Euler.BanachGeometricTail
public import RequestProject.Euler.BanachLocalRemainder

/-! The normalized expanding coefficient of an actual nonlinear
backward orbit converges. Its limit and error follow from the true
quadratic remainder, rather than a prescribed asymptotic expansion. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_unstableCoefficient_of_quadratic_backward_orbit
    {F : E → E} (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {a b K M : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hab : a * b ^ 2 < 1) (hPL : ∀ v, P (L v) = a • P v)
    (x : ℕ → E) (hrec : ∀ n, F (x (n + 1)) = x n)
    (hnorm : ∀ n, ‖x n‖ ≤ M * b ^ n)
    (hquad : ∀ n, ‖banachLocalRemainder F (x (n + 1))‖ ≤ K * ‖x (n + 1)‖ ^ 2) :
    ∃ c : E, Tendsto (fun n : ℕ => a ^ n • P (x n)) atTop (𝓝 c) ∧
      (∀ n : ℕ, ‖a ^ n • P (x n) - c‖ ≤
        ((‖P‖ * K * M ^ 2 * b ^ 2) / (1 - a * b ^ 2)) * (a * b ^ 2) ^ n) ∧
      ‖c - P (x 0)‖ ≤ (‖P‖ * K * M ^ 2 * b ^ 2) / (1 - a * b ^ 2) := by
  let v : ℕ → E := fun n => a ^ n • P (banachLocalRemainder F (x (n + 1)))
  let w : ℕ → E := fun n => a ^ n • P (x n)
  have hv (n : ℕ) : ‖v n‖ ≤ (‖P‖ * K * M ^ 2 * b ^ 2) * (a * b ^ 2) ^ n := by
    have hxsq : ‖x (n + 1)‖ ^ 2 ≤ (M * b ^ (n + 1)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm (n + 1)) 2
    have hb2 : (b ^ (n + 1)) ^ 2 = b ^ 2 * (b ^ 2) ^ n := by
      rw [pow_succ b n, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      ring
    change ‖a ^ n • P (banachLocalRemainder F (x (n + 1)))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha.le n)]
    calc
      _ ≤ a ^ n * (‖P‖ * ‖banachLocalRemainder F (x (n + 1))‖) :=
        mul_le_mul_of_nonneg_left (P.le_opNorm _) (pow_nonneg ha.le n)
      _ ≤ a ^ n * (‖P‖ * (K * ‖x (n + 1)‖ ^ 2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hquad n) (norm_nonneg P)) (pow_nonneg ha.le n)
      _ ≤ a ^ n * (‖P‖ * (K * (M * b ^ (n + 1)) ^ 2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxsq hK) (norm_nonneg P))
        (pow_nonneg ha.le n)
      _ = _ := by rw [mul_pow, hb2, mul_pow]; ring
  have hpoint (n : ℕ) : x n = L (x (n + 1)) + banachLocalRemainder F (x (n + 1)) := by
    rw [← hrec n, banachLocalRemainder, hderiv]
    abel
  have hw (n : ℕ) : w (n + 1) = w n - v n := by
    have hp := congrArg P (hpoint n)
    rw [P.map_add, hPL] at hp
    have he : a • P (x (n + 1)) = P (x n) - P (banachLocalRemainder F (x (n + 1))) := by
      rw [hp]
      abel
    dsimp only [w, v]
    rw [pow_succ, mul_smul, he, smul_sub]
  obtain ⟨c, hlim, herr, hc⟩ := exists_limit_of_geometric_increments
    (mul_nonneg ha.le (sq_nonneg b)) hab hv hw
  refine ⟨c, hlim, herr, ?_⟩
  simpa only [w, pow_zero, one_smul] using hc

theorem ne_zero_of_quadratic_distance {c ξ : E} {C : ℝ} (hξ : ξ ≠ 0)
    (hsmall : C * ‖ξ‖ < 1) (hclose : ‖c - ξ‖ ≤ C * ‖ξ‖ ^ 2) : c ≠ 0 := by
  intro hc
  rw [hc, zero_sub, norm_neg] at hclose
  have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have ht := mul_lt_mul_of_pos_right hsmall hp
  nlinarith

end Euler2D

end
