module

public import RequestProject.Euler.BanachAncientFlowCells
public import RequestProject.Euler.BanachObservableAsymptotic

/-! A genuine sampled full-space asymptotic and the true uniform
quadratic material-flow error give a full expansion throughout every
negative-time cell, with the same uniform error constant. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem banachAncientCurve_cell_asymptotic
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
    (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
    (hreturn : ∀ n, X (z (n + 1)) T = z n)
    (c : ℝ → E) (A : ℝ → E →L[ℝ] E) (v : E) {δ κ a b C B M : ℝ}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hquad : ∀ h : E, ‖h‖ ≤ δ → ∀ s ∈ Icc (0 : ℝ) T,
      ‖X (c 0 + h) s - c s - A s h‖ ≤ κ * ‖h‖ ^ 2)
    (hsmall : ∀ n, ‖z n - c 0‖ ≤ δ)
    (hnorm : ∀ n, ‖z n - c 0‖ ≤ C * b ^ n)
    (herror : ∀ n, ‖(z n - c 0) - (a⁻¹) ^ n • v‖ ≤ B * (b ^ 2) ^ n)
    (hA : ∀ s ∈ Icc (0 : ℝ) T, ‖A s‖ ≤ M)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ‖banachAncientCurve hT X z (-((n + 1 : ℕ) : ℝ) * T + s) - c s -
        (a⁻¹) ^ (n + 1) • A s v‖ ≤ (κ * C ^ 2 + M * B) * (b ^ 2) ^ (n + 1) := by
  have hq (k : ℕ) :
      ‖(X (c 0 + (z k - c 0)) s - c s) - A s (z k - c 0)‖ ≤ κ * ‖z k - c 0‖ ^ 2 :=
    hquad _ (hsmall k) s hs
  have he := observable_quadratic_backward_asymptotic
    (fun h : E => X (c 0 + h) s - c s) (A s) (fun k => z k - c 0) v hκ hnorm herror hq (n + 1)
  change ‖(X (c 0 + (z (n + 1) - c 0)) s - c s) - (a⁻¹) ^ (n + 1) • A s v‖ ≤ _ at he
  rw [show c 0 + (z (n + 1) - c 0) = z (n + 1) by abel] at he
  rw [banachAncientCurve_eq_shifted_flow hT hX hz hreturn n hs]
  calc
    _ ≤ (κ * C ^ 2 + ‖A s‖ * B) * (b ^ 2) ^ (n + 1) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hA s hs) hB)) (pow_nonneg (sq_nonneg b) _)

end Euler2D

end
