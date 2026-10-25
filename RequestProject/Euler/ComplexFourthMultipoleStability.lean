module

public import RequestProject.Euler.ExteriorFieldDerivatives

/-! An explicit pointwise stability estimate for the true fourth
moment velocity field. Only a lower bound on both radii is needed;
the segment between the two points need not avoid the origin. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace Euler2D

def fourthMomentVelocityField (M z : ℂ) : ℂ :=
  I / (2 * Real.pi) * M * (conj z ^ 5)⁻¹

theorem norm_pow_five_sub_pow_five_le {u v : ℂ} {K : ℝ}
    (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) :
    ‖u ^ 5 - v ^ 5‖ ≤ 5 * K ^ 4 * ‖u - v‖ := by
  have hK : 0 ≤ K := (norm_nonneg u).trans hu
  have hfactor : u ^ 5 - v ^ 5 = (u - v) * ∑ j : Fin 5, u ^ (4 - (j : ℕ)) * v ^ (j : ℕ) := by
    norm_num [Fin.sum_univ_succ] <;> ring
  have hterm (j : Fin 5) : ‖u ^ (4 - (j : ℕ)) * v ^ (j : ℕ)‖ ≤ K ^ 4 := by
    rw [norm_mul, norm_pow, norm_pow]
    calc
      _ ≤ K ^ (4 - (j : ℕ)) * K ^ (j : ℕ) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg u) hu _) (pow_le_pow_left₀ (norm_nonneg v) hv _)
          (by positivity) (by positivity)
      _ = K ^ 4 := by rw [← pow_add]; congr 1; omega
  have hsum : ‖∑ j : Fin 5, u ^ (4 - (j : ℕ)) * v ^ (j : ℕ)‖ ≤ 5 * K ^ 4 := by
    calc
      _ ≤ ∑ j : Fin 5, ‖u ^ (4 - (j : ℕ)) * v ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 5, K ^ 4 := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp
  rw [hfactor, norm_mul]
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans_eq (by ring)

theorem norm_inv_conj_pow_five_sub_le {z w : ℂ} {d : ℝ}
    (hd : 0 < d) (hz : d ≤ ‖z‖) (hw : d ≤ ‖w‖) :
    ‖(conj z ^ 5)⁻¹ - (conj w ^ 5)⁻¹‖ ≤ (5 / d ^ 6) * ‖z - w‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hd.trans_le hz)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hd.trans_le hw)
  have hcz : conj z ≠ 0 := by
    intro hh
    exact hz0 (by simpa only [map_zero, conj_conj] using congrArg conj hh)
  have hcw : conj w ≠ 0 := by
    intro hh
    exact hw0 (by simpa only [map_zero, conj_conj] using congrArg conj hh)
  have ha : ‖(conj z)⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv, norm_conj]
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hd hz
  have hb : ‖(conj w)⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv, norm_conj]
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hd hw
  have hmid : ‖conj w - conj z‖ = ‖z - w‖ := by rw [← map_sub, norm_conj, norm_sub_rev]
  have hinv : ‖(conj z)⁻¹ - (conj w)⁻¹‖ ≤ d⁻¹ * ‖z - w‖ * d⁻¹ := by
    rw [inv_sub_inv' hcz hcw, norm_mul, norm_mul, hmid]
    exact mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hb (norm_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hd.le) (norm_nonneg _))
  have hp := norm_pow_five_sub_pow_five_le ha hb
  have hp' : ‖(conj z ^ 5)⁻¹ - (conj w ^ 5)⁻¹‖ ≤
      5 * (d⁻¹) ^ 4 * ‖(conj z)⁻¹ - (conj w)⁻¹‖ := by
    simpa only [inv_pow] using hp
  calc
    _ ≤ 5 * (d⁻¹) ^ 4 * (d⁻¹ * ‖z - w‖ * d⁻¹) :=
      hp'.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = _ := by field_simp [hd.ne'] <;> ring

theorem norm_fourthMomentVelocityField_sub_le (M : ℂ) {z w : ℂ} {d : ℝ}
    (hd : 0 < d) (hz : d ≤ ‖z‖) (hw : d ≤ ‖w‖) :
    ‖fourthMomentVelocityField M z - fourthMomentVelocityField M w‖ ≤
      (5 / (2 * Real.pi * d ^ 6)) * ‖M‖ * ‖z - w‖ := by
  have hcoef : ‖(I : ℂ) / (2 * Real.pi)‖ = 1 / (2 * Real.pi) := by
    norm_num [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have heq : fourthMomentVelocityField M z - fourthMomentVelocityField M w =
      I / (2 * Real.pi) * M * ((conj z ^ 5)⁻¹ - (conj w ^ 5)⁻¹) := by
    unfold fourthMomentVelocityField
    ring
  rw [heq, norm_mul, norm_mul, hcoef]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ‖M‖ * ((5 / d ^ 6) * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (norm_inv_conj_pow_five_sub_le hd hz hw) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero, hd.ne'] <;> ring

end Euler2D

end
