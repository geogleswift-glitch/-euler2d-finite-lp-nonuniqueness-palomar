module

public import RequestProject.Euler.CircularMaterialTransferProfile

/-! The same actual moment profile has a nonzero transfer ratio in
every prescribed sufficiently small interval. The ratio may therefore
be chosen after fixed self-field and clock constants, before rho and
all physical scales. No previously chosen ratio is silently shrunk. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_scale_ratio_below {σ ν δ d : ℝ} {κ : ℂ} {N : ℝ → ℂ}
    (h : LaplaceHyp σ ν δ d κ N) (β : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ b ∈ Ioo (0 : ℝ) (min B (1 / 4)),
      bilateral N ((b : ℂ) * (σ + β * I)) ≠ 0 := by
  let U : ℝ := min B (1 / 4)
  have hU : 0 < U := lt_min hB (by norm_num)
  have hU4 : U ≤ 1 / 4 := min_le_right _ _
  by_contra hall
  push_neg at hall
  apply (bilateral_laplace_theorem h β).2.2 (U / 2)
    ⟨by positivity, by linarith⟩
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds
    (show U / 2 ∈ Ioo (0 : ℝ) U from ⟨by positivity, by linarith⟩))] with b hb
  exact hall b hb

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_nonzero_transfer_ratio_below {B : ℝ} (hB : 0 < B) :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4), b < B ∧
      bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 := by
  obtain ⟨b, hb, hne⟩ := exists_scale_ratio_below P.laplace (5 / 4 : ℝ) hB
  refine ⟨b, ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩,
    hb.2.trans_le (min_le_left _ _), ?_⟩
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hne

end CircularMaterialTransferProfile
end Euler2D

end
