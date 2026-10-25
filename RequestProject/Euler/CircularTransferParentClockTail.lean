module

public import RequestProject.Euler.CircularTransferFixedEntry
public import RequestProject.Euler.PolynomialForcingTailScale

/-! The same nonzero original transfer chooses one entrance before
rho, with the actual parent-clock tail small relative to its seed. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_fixed_transfer_entry_parent_clock_tail {b B θ : ℝ}
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
      (∀ ρ : ℝ, Real.exp (b * sigma * s₀) * (B * ρ ^ 6 * polynomialForcingTail sigma (b * s₀)) ≤
        θ * H * ρ ^ 6) := by
  obtain ⟨s₀, hs₀, H, hH, hHdef, hseed, hpert, htail⟩ :=
    P.exists_fixed_transfer_entry_and_polynomial_tail hb hne (mul_nonneg hb.1.le hB) hθ
  refine ⟨s₀, hs₀, H, hH, hHdef, hseed, hpert, ?_⟩
  intro ρ
  have hclock := polynomialForcingTail_mul_clock P.laplace.sigma_pos hb.1
    (by linarith [hb.2] : b ≤ 1) hs₀
  calc
    _ ≤ Real.exp (b * sigma * s₀) *
        ((b * B) * ρ ^ 6 * polynomialForcingTail (b * sigma) s₀) := by
      have hh := mul_le_mul_of_nonneg_left hclock
        (mul_nonneg (Real.exp_pos (b * sigma * s₀)).le
          (mul_nonneg hB (by positivity : 0 ≤ ρ ^ 6)))
      convert hh using 1 <;> ring
    _ ≤ _ := htail ρ

end CircularMaterialTransferProfile
end Euler2D

end
