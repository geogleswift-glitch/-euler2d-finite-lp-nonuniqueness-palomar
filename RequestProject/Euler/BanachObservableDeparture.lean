module

public import Mathlib

/-! A nonzero derivative of an actual observable remains detectable
on a sufficiently flat nonlinear graph through the growing direction. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_observable_departure_cone {φ : E → F} {D : E →L[ℝ] F}
    (hφ : HasFDerivAt φ D 0) (g : E) (hg : D g ≠ 0) :
    ∃ ε > 0, ∃ r > 0, ∀ (t : ℝ) (x : E), x ∈ ball 0 r →
      ‖x‖ ≤ 2 * |t| * ‖g‖ → ‖x - t • g‖ ≤ ε * |t| * ‖g‖ →
        (‖D g‖ / 2) * |t| ≤ ‖φ x - φ 0‖ := by
  let p := ‖D g‖
  let b := ‖g‖
  let A := ‖D‖
  have hp : 0 < p := norm_pos_iff.mpr hg
  have hb : 0 ≤ b := norm_nonneg g
  have hA : 0 ≤ A := norm_nonneg D
  let ε := p / (8 * (b + 1) * (A + 1))
  have hden : 0 < 8 * (b + 1) * (A + 1) := by positivity
  have hε : 0 < ε := div_pos hp hden
  have heq : ε * (8 * (b + 1) * (A + 1)) = p := div_mul_cancel₀ p hden.ne'
  have hcoarse : ε * (2 * b + A * b) ≤ p / 2 := by
    have hab := mul_nonneg (mul_nonneg hε.le hA) hb
    have hae := mul_nonneg hε.le hA
    have hbe := mul_nonneg hε.le hb
    nlinarith
  have hsmall : ∀ᶠ x : E in 𝓝 0, ‖φ x - φ 0 - D x‖ ≤ ε * ‖x‖ := by
    simpa only [sub_zero] using hφ.isLittleO.bound hε
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨ε, hε, r, hr, ?_⟩
  intro t x hx hnorm hgraph
  have he : ‖φ x - φ 0 - t • D g‖ ≤ |t| * (p / 2) := by
    have hid : φ x - φ 0 - t • D g = (φ x - φ 0 - D x) + D (x - t • g) := by
      rw [D.map_sub, D.map_smul]
      abel
    rw [hid]
    calc
      _ ≤ ‖φ x - φ 0 - D x‖ + ‖D (x - t • g)‖ := norm_add_le _ _
      _ ≤ ε * ‖x‖ + A * ‖x - t • g‖ := add_le_add (hrem hx) (D.le_opNorm _)
      _ ≤ ε * (2 * |t| * b) + A * (ε * |t| * b) := add_le_add
        (mul_le_mul_of_nonneg_left hnorm hε.le) (mul_le_mul_of_nonneg_left hgraph hA)
      _ = |t| * (ε * (2 * b + A * b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoarse (abs_nonneg t)
  have ht := norm_sub_le (φ x - φ 0) (φ x - φ 0 - t • D g)
  have hid : (φ x - φ 0) - (φ x - φ 0 - t • D g) = t • D g := by abel
  rw [hid, norm_smul, Real.norm_eq_abs] at ht
  change |t| * p ≤ ‖φ x - φ 0‖ + ‖φ x - φ 0 - t • D g‖ at ht
  change (p / 2) * |t| ≤ _
  nlinarith

end Euler2D

end
