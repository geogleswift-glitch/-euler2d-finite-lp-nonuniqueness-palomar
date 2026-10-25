module

public import RequestProject.Euler.CircularMaterialRetardedDifferentiability

/-! The ORIGINAL retarded response factors exactly by rho^6.
Its ORIGINAL normalization at minus infinity makes the propagated
past tail small uniformly in rho, so the lookback length can be
chosen before the physical shrinking scale. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem retardedSol_mul_coefficient (c z a K : ℂ) (N : ℝ → ℂ) (t : ℝ) :
    retardedSol c z (a * K) N t = a * retardedSol c z K N t := by
  unfold retardedSol
  ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem retarded_transfer_rho_factor (b ρ t : ℝ) :
    retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
      ((ρ : ℂ) ^ 6 * Kstar) P.moment t =
        (ρ : ℂ) ^ 6 * retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          Kstar P.moment t := retardedSol_mul_coefficient _ _ _ _ _ _

theorem norm_retarded_transfer_rho_factor {ρ : ℝ} (hρ : 0 ≤ ρ) (b t : ℝ) :
    ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
      ((ρ : ℂ) ^ 6 * Kstar) P.moment t‖ =
        ρ ^ 6 * ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          Kstar P.moment t‖ := by
  rw [P.retarded_transfer_rho_factor, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρ]

theorem tendsto_normalized_retarded_transfer_atBot {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) :
    Tendsto (fun t : ℝ => Real.exp (-(b * sigma) * t) *
      ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment t‖)
      atBot (𝓝 0) := by
  have hz0 : 0 < (((b : ℂ) * (sigma + 5 / 4 * I) : ℂ)).re := by
    simpa using mul_pos hb.1 sigma_pos
  have hz1 : (((b : ℂ) * (sigma + 5 / 4 * I) : ℂ)).re < sigma := by
    have hb1 : b < 1 := by linarith only [hb.2]
    simpa using mul_lt_of_lt_one_left sigma_pos hb1
  have hh := (retardedSol_spec P.laplace.expWindow hz0 hz1 ((b : ℂ) * lamStar) Kstar).2.1.norm
  have hc : (((b : ℂ) * lamStar) : ℂ).re = b * sigma := by simp [lamStar]
  simpa only [norm_mul, norm_cexp_neg_mul, hc, norm_zero] using hh

theorem tendsto_retarded_lookback_tail {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (s d : ℝ) :
    Tendsto (fun L : ℝ =>
      ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        Kstar P.moment (s - L)‖ * Real.exp (b * sigma * (L + d))) atTop (𝓝 0) := by
  have htime : Tendsto (fun L : ℝ => s - L) atTop atBot := by
    apply tendsto_atBot.mpr
    intro B
    filter_upwards [eventually_ge_atTop (s - B)] with L hL
    linarith only [hL]
  have hh : Tendsto (fun L : ℝ => Real.exp (b * sigma * (s + d)) *
      (Real.exp (-(b * sigma) * (s - L)) *
        ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          Kstar P.moment (s - L)‖)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((P.tendsto_normalized_retarded_transfer_atBot hb).comp htime).const_mul (Real.exp (b * sigma * (s + d)))
  apply hh.congr
  intro L
  have he : Real.exp (b * sigma * (L + d)) =
      Real.exp (b * sigma * (s + d)) * Real.exp (-(b * sigma) * (s - L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem eventually_retarded_lookback_tail_uniform_rho {b ζ : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (hζ : 0 < ζ) (s d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ ρ : ℝ, 0 ≤ ρ →
      ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (s - L)‖ * Real.exp (b * sigma * (L + d)) ≤ ζ * ρ ^ 6 := by
  filter_upwards [(P.tendsto_retarded_lookback_tail hb s d).eventually (gt_mem_nhds hζ)] with L hL
  intro ρ hρ
  rw [P.norm_retarded_transfer_rho_factor hρ]
  calc
    _ = (‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        Kstar P.moment (s - L)‖ * Real.exp (b * sigma * (L + d))) * ρ ^ 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hL.le (pow_nonneg hρ 6)

end CircularMaterialTransferProfile
end Euler2D

end
