module

public import RequestProject.Euler.BanachAncientCurve

/-! The ancient curve is exactly the actual material flow on every
negative-time cell. Uniform flow estimates therefore apply between
the discrete return samples without an interpolation assumption. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem banachAncientCurve_eq_flow_cell
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
    (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
    (hreturn : ∀ n, X (z (n + 1)) T = z n) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (-((n + 1 : ℕ) : ℝ) * T) (-(n : ℝ) * T)) :
    banachAncientCurve hT X z t = X (z (n + 1)) (t + (n + 1 : ℕ) * T) := by
  rw [banachAncientCurve_eq_segment hT hX hz hreturn (n + 1) ht.1, banachBackwardSegment]
  dsimp only
  rw [if_pos ht.2]

theorem banachAncientCurve_eq_shifted_flow
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
    (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
    (hreturn : ∀ n, X (z (n + 1)) T = z n) (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    banachAncientCurve hT X z (-((n + 1 : ℕ) : ℝ) * T + s) = X (z (n + 1)) s := by
  have ht : -((n + 1 : ℕ) : ℝ) * T + s ∈
      Icc (-((n + 1 : ℕ) : ℝ) * T) (-(n : ℝ) * T) := by
    constructor <;> push_cast <;> nlinarith [hs.1, hs.2]
  rw [banachAncientCurve_eq_flow_cell hT hX hz hreturn n ht]
  congr 1
  ring

theorem banachAncientCurve_quadratic_cell_estimate
    {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
    (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
    (hreturn : ∀ n, X (z (n + 1)) T = z n)
    (c : ℝ → E) (A : ℝ → E →L[ℝ] E) {δ C : ℝ}
    (hquad : ∀ h : E, ‖h‖ ≤ δ → ∀ s ∈ Icc (0 : ℝ) T,
      ‖X (c 0 + h) s - c s - A s h‖ ≤ C * ‖h‖ ^ 2)
    (n : ℕ) (hsmall : ‖z (n + 1) - c 0‖ ≤ δ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ‖banachAncientCurve hT X z (-((n + 1 : ℕ) : ℝ) * T + s) - c s -
      A s (z (n + 1) - c 0)‖ ≤ C * ‖z (n + 1) - c 0‖ ^ 2 := by
  rw [banachAncientCurve_eq_shifted_flow hT hX hz hreturn n hs]
  have he := hquad (z (n + 1) - c 0) hsmall s hs
  rwa [show c 0 + (z (n + 1) - c 0) = z (n + 1) by abel] at he

end Euler2D

end
