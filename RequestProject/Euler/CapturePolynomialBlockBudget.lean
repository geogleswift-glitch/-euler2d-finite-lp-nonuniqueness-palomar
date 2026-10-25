module

public import Mathlib

/-! The true fourth-degree source on each fixed capture block has a
uniform finite weighted sum. The constant is fixed before the seed,
rho and the finite endpoint; the actual block clock is retained. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Euler2D

theorem exists_capture_polynomial_block_budget {lam T : ℝ}
    (hlam : 1 < lam) (hT : 0 ≤ T) :
    ∃ F > 0, ∀ {S B ρ : ℝ}, 0 ≤ S → 0 ≤ B → ∀ N : ℕ,
      (∑ j ∈ Finset.range N, (B * ρ ^ 6 * (1 + S + ((j + 1 : ℕ) : ℝ) * T) ^ 4) /
        lam ^ (j + 1)) ≤ F * B * ρ ^ 6 * (1 + S) ^ 4 := by
  have hl0 : 0 < lam := zero_lt_one.trans hlam
  have hnorm : ‖lam⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hl0.le)]
    exact (inv_lt_one₀ hl0).mpr hlam
  let g : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ 4 * (lam⁻¹) ^ (j + 1)
  have hg : Summable g :=
    (summable_pow_mul_geometric_of_norm_lt_one 4 hnorm).comp_injective
      (show Function.Injective (fun j : ℕ => j + 1) from fun _ _ h => Nat.add_right_cancel h)
  have hg0 (j : ℕ) : 0 ≤ g j := by dsimp only [g]; positivity
  let F := (1 + T) ^ 4 * (∑' j, g j) + 1
  have hF : 0 < F := by
    have hs : 0 ≤ ∑' j, g j := tsum_nonneg hg0
    dsimp only [F]
    positivity
  refine ⟨F, hF, ?_⟩
  intro S B ρ hS hB N
  have hcoef : 0 ≤ B * ρ ^ 6 * (1 + S) ^ 4 := by positivity
  have hpoint (j : ℕ) :
      (B * ρ ^ 6 * (1 + S + ((j + 1 : ℕ) : ℝ) * T) ^ 4) / lam ^ (j + 1) ≤
        (B * ρ ^ 6 * (1 + S) ^ 4 * (1 + T) ^ 4) * g j := by
    have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have h₁ := mul_le_mul_of_nonneg_left hj (show 0 ≤ 1 + S by linarith)
    have h₂ := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + S by linarith)
      (show 0 ≤ ((j + 1 : ℕ) : ℝ) * T by positivity)
    have hh : 1 + S + ((j + 1 : ℕ) : ℝ) * T ≤ (1 + S) * (1 + T) * ((j + 1 : ℕ) : ℝ) := by
      nlinarith only [h₁, h₂]
    have hp := pow_le_pow_left₀ (show 0 ≤ 1 + S + ((j + 1 : ℕ) : ℝ) * T by positivity) hh 4
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ B * ρ ^ 6 by positivity)
    have hd := div_le_div_of_nonneg_right hm (pow_nonneg hl0.le (j + 1))
    exact hd.trans_eq (by simp only [g, mul_pow, div_eq_mul_inv, inv_pow]; ring)
  have hsum := hg.sum_le_tsum (Finset.range N) (fun j _ => hg0 j)
  calc
    _ ≤ ∑ j ∈ Finset.range N, (B * ρ ^ 6 * (1 + S) ^ 4 * (1 + T) ^ 4) * g j :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = (B * ρ ^ 6 * (1 + S) ^ 4 * (1 + T) ^ 4) * ∑ j ∈ Finset.range N, g j := by
      rw [Finset.mul_sum]
    _ ≤ (B * ρ ^ 6 * (1 + S) ^ 4 * (1 + T) ^ 4) * ∑' j, g j :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by
      dsimp only [F]
      nlinarith only [hcoef]

end Euler2D

end
