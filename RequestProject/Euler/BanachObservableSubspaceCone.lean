module

public import RequestProject.Euler.BanachObservableDeparture

/-! A quantitative observable bound valid for every direction on a
subspace with a common derivative lower bound. This includes every
complex phase of the circular growing mode. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_observable_departure_subspace_cone {φ : E → F} {D : E →L[ℝ] F}
    (hφ : HasFDerivAt φ D 0) {m : ℝ} (hm : 0 < m) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ r > 0, ∀ x α : E, x ∈ ball 0 r →
      m * ‖α‖ ≤ ‖D α‖ → ‖x - α‖ ≤ ε * ‖α‖ →
      (m / 2) * ‖α‖ ≤ ‖φ x - φ 0‖ := by
  let A := ‖D‖
  let ε := min 1 (m / (8 * (A + 1)))
  have hA : 0 ≤ A := norm_nonneg D
  have hden : 0 < 8 * (A + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hm hden)
  have hεOne : ε ≤ 1 := min_le_left _ _
  have hprod : ε * (8 * (A + 1)) ≤ m :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hcoarse : ε * (2 + A) ≤ m / 2 := by
    have hεA : 0 ≤ ε * A := mul_nonneg hε.le hA
    nlinarith only [hprod, hεA, hε.le]
  have hsmall : ∀ᶠ x : E in 𝓝 0, ‖φ x - φ 0 - D x‖ ≤ ε * ‖x‖ := by
    simpa only [sub_zero] using hφ.isLittleO.bound hε
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨ε, hε, hεOne, r, hr, ?_⟩
  intro x α hx hlinear hcone
  have hxnorm : ‖x‖ ≤ 2 * ‖α‖ := by
    have htriangle := norm_add_le (x - α) α
    rw [sub_add_cancel] at htriangle
    have he := mul_le_mul_of_nonneg_right hεOne (norm_nonneg α)
    linarith only [htriangle, hcone, he]
  have herr : ‖φ x - φ 0 - D α‖ ≤ (m / 2) * ‖α‖ := by
    have hid : φ x - φ 0 - D α = (φ x - φ 0 - D x) + D (x - α) := by
      rw [D.map_sub]
      abel
    rw [hid]
    calc
      _ ≤ ‖φ x - φ 0 - D x‖ + ‖D (x - α)‖ := norm_add_le _ _
      _ ≤ ε * ‖x‖ + A * ‖x - α‖ := add_le_add (hrem hx) (D.le_opNorm _)
      _ ≤ ε * (2 * ‖α‖) + A * (ε * ‖α‖) := add_le_add
        (mul_le_mul_of_nonneg_left hxnorm hε.le) (mul_le_mul_of_nonneg_left hcone hA)
      _ = (ε * (2 + A)) * ‖α‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoarse (norm_nonneg α)
  have htriangle := norm_sub_le (φ x - φ 0) (φ x - φ 0 - D α)
  have hid : (φ x - φ 0) - (φ x - φ 0 - D α) = D α := by abel
  rw [hid] at htriangle
  linarith only [hlinear, htriangle, herr]

end Euler2D

end
