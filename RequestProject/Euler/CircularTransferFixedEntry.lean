module

public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.PolynomialForcingTail

/-! One late transfer entrance and its positive seed coefficient are
chosen from the same original moment profile before rho. At that same
entrance the full polynomial forcing tail is seed-relative small. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_fixed_transfer_entry_and_polynomial_tail {b B θ : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hne : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0)
    (hB : 0 ≤ B) (hθ : 0 < θ) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∃ H : ℝ, 0 < H ∧
      H = (‖Kstar * bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I))‖ / 4) *
        Real.exp (b * sigma * s₀) ∧
      (∀ ρ : ℝ, 0 ≤ ρ → 2 * H * ρ ^ 6 ≤
        ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖) ∧
      (∀ (ρ : ℝ) (W : ℂ), 0 ≤ ρ →
        ‖W - retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖ ≤ H * ρ ^ 6 → H * ρ ^ 6 ≤ ‖W‖) ∧
      (∀ ρ : ℝ, Real.exp (b * sigma * s₀) * (B * ρ ^ 6 * polynomialForcingTail (b * sigma) s₀) ≤
        θ * H * ρ ^ 6) := by
  let c : ℂ := (b : ℂ) * lamStar
  let z : ℂ := (b : ℂ) * (sigma + 5 / 4 * I)
  let Y := retardedSol c z Kstar P.moment
  let κ : ℝ := ‖Kstar * bilateral P.moment z‖
  have hσ : 0 < sigma := P.laplace.sigma_pos
  have ha : 0 < b * sigma := mul_pos hb.1 hσ
  have hκ : 0 < κ := norm_pos_iff.mpr (mul_ne_zero Kstar_ne_zero hne)
  have hz0 : 0 < z.re := by dsimp only [z]; simp; exact ha
  have hz1 : z.re < sigma := by
    dsimp only [z]
    simp
    nlinarith [hb.2]
  obtain ⟨_, _, hlim⟩ := retardedSol_spec P.laplace.expWindow hz0 hz1 c Kstar
  have hnorm : ∀ᶠ s : ℝ in atTop, κ / 2 < ‖exp (-c * s) * Y s‖ :=
    hlim.norm.eventually (lt_mem_nhds (half_lt_self hκ))
  have htail := (tendsto_polynomialForcingTail ha).const_mul B
  simp only [mul_zero] at htail
  have htail' : ∀ᶠ s : ℝ in atTop, B * polynomialForcingTail (b * sigma) s ≤ θ * (κ / 4) :=
    (htail.eventually (gt_mem_nhds (mul_pos hθ (by positivity : 0 < κ / 4)))).mono (fun _ h => h.le)
  obtain ⟨s₀, hs₀, hnorm₀, htail₀⟩ := ((eventually_ge_atTop (0 : ℝ)).and (hnorm.and htail')).exists
  let H : ℝ := (κ / 4) * Real.exp (b * sigma * s₀)
  have hH : 0 < H := mul_pos (by positivity) (Real.exp_pos _)
  have hc : c.re = b * sigma := by simp [c, lamStar]
  have hY : 2 * H ≤ ‖Y s₀‖ := by
    rw [norm_mul, norm_cexp_neg_mul, hc] at hnorm₀
    have hh := mul_le_mul_of_nonneg_right hnorm₀.le (Real.exp_pos (b * sigma * s₀)).le
    have he : Real.exp (-(b * sigma) * s₀) * Real.exp (b * sigma * s₀) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    have heq : (Real.exp (-(b * sigma) * s₀) * ‖Y s₀‖) * Real.exp (b * sigma * s₀) = ‖Y s₀‖ := by
      calc
        _ = (Real.exp (-(b * sigma) * s₀) * Real.exp (b * sigma * s₀)) * ‖Y s₀‖ := by ring
        _ = _ := by rw [he, one_mul]
    rw [heq] at hh
    dsimp only [H]
    nlinarith only [hh]
  have hscaled (ρ : ℝ) (hρ : 0 ≤ ρ) :
      ‖retardedSol c z ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖ = ρ ^ 6 * ‖Y s₀‖ := by
    have heq : retardedSol c z ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀ = (ρ : ℂ) ^ 6 * Y s₀ := by
      dsimp only [Y, retardedSol]
      ring
    rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ]
  have hseed (ρ : ℝ) (hρ : 0 ≤ ρ) :
      2 * H * ρ ^ 6 ≤ ‖retardedSol c z ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀‖ := by
    rw [hscaled ρ hρ]
    nlinarith only [mul_le_mul_of_nonneg_right hY (pow_nonneg hρ 6)]
  refine ⟨s₀, hs₀, H, hH, rfl, hseed, ?_, ?_⟩
  · intro ρ W hρ hclose
    have hs := hseed ρ hρ
    have hn := norm_le_norm_sub_add (retardedSol c z ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀) W
    rw [norm_sub_rev] at hn
    nlinarith only [hs, hn, hclose]
  · intro ρ
    have hh := mul_le_mul_of_nonneg_right htail₀ (by positivity : 0 ≤ Real.exp (b * sigma * s₀) * ρ ^ 6)
    dsimp only [H]
    convert hh using 1 <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
