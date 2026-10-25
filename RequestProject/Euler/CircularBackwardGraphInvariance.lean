module

public import RequestProject.Euler.CircularLocalBackwardGraph

/-! On a genuinely constructed common neighborhood, the actual return
map takes the weighted graph into itself in both discrete directions.
This does not claim C³ regularity or continuous-time invariance. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

namespace IsLocalWeightedBackwardGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem exists_twoSided_invariant_radius (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (hF0 : F 0 = 0) (hF : ContinuousAt F 0) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ η →
      ‖P (x ξ 1)‖ ≤ r / 2 ∧
      ‖P (F (x ξ 0))‖ ≤ r / 2 ∧
      x (P (x ξ 1)) = (fun n => x ξ (n + 1)) ∧
      x (P (F (x ξ 0))) = (fun n => Nat.casesOn n (F (x ξ 0)) (fun k => x ξ k)) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  let c := r / (2 * (‖P‖ + 1))
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hF c hc
  let η := min (r / 4) (min (δ / 4) (min (r / (4 * ρ)) (r / (4 * (‖P‖ + 1)))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηr : η ≤ r / 2 := by
    have hh : η ≤ r / 4 := min_le_left _ _
    linarith
  refine ⟨η, hη, hηr, ?_⟩
  intro ξ hξ hξη
  have hξr : ‖ξ‖ ≤ r / 2 := hξη.trans hηr
  have hξδ : ‖ξ‖ ≤ δ / 4 := hξη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hξρ : ‖ξ‖ ≤ r / (4 * ρ) :=
    hξη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hξP : ‖ξ‖ ≤ r / (4 * (‖P‖ + 1)) :=
    hξη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnorm0 : ‖x ξ 0‖ ≤ 2 * ‖ξ‖ := by
    simpa only [pow_zero, mul_one] using h.norm_le ξ hξ hξr 0
  have hnorm1 : ‖x ξ 1‖ ≤ 2 * ‖ξ‖ := by
    have hh := h.norm_le ξ hξ hξr 1
    have hi : ρ⁻¹ ≤ 1 := by
      simpa only [pow_one] using (real_weight_inverse_pow_facts hρ 1).2.2.1
    have hmul := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2 * ‖ξ‖)
    simp only [pow_one] at hh
    nlinarith
  have hback : ‖P (x ξ 1)‖ ≤ r / 2 := by
    have hp := (le_div_iff₀ (by positivity : 0 < 4 * (‖P‖ + 1))).mp hξP
    calc
      _ ≤ ‖P‖ * ‖x ξ 1‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (2 * ‖ξ‖) := mul_le_mul_of_nonneg_left hnorm1 (norm_nonneg P)
      _ ≤ r / 2 := by nlinarith [norm_nonneg P, norm_nonneg ξ]
  have hdist : dist (x ξ 0) 0 < δ := by
    rw [dist_zero_right]
    linarith
  have hFc : ‖F (x ξ 0)‖ < c := by
    have hh := hδF hdist
    simpa only [hF0, dist_zero_right] using hh
  have hcden : c * (2 * (‖P‖ + 1)) = r := by
    dsimp only [c]
    field_simp
  have hforward : ‖P (F (x ξ 0))‖ ≤ r / 2 := by
    calc
      _ ≤ ‖P‖ * ‖F (x ξ 0)‖ := P.le_opNorm _
      _ ≤ ‖P‖ * c := mul_le_mul_of_nonneg_left hFc.le (norm_nonneg P)
      _ ≤ r / 2 := by nlinarith [norm_nonneg P]
  have hweighted : 2 * ρ * ‖ξ‖ ≤ r := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * ρ)).mp hξρ
    nlinarith [norm_nonneg ξ]
  have himage : ‖F (x ξ 0)‖ ≤ r := by
    have hh : c ≤ r := by nlinarith [norm_nonneg P]
    exact hFc.le.trans hh
  exact ⟨hback, hforward, h.backward_shift hρ hP hξ hξr hback,
    h.forward_shift hρ hP hξ hξr hweighted himage hforward⟩

end IsLocalWeightedBackwardGraph

end Euler2D

end
