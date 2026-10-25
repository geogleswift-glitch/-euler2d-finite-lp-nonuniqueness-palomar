module

public import RequestProject.Euler.BanachLocalBackwardGraph

/-! Local invariance follows from uniqueness of the actual weighted
backward orbit. Only local commutation with the return map is needed. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsLocalWeightedBackwardGraph

variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem exists_commuting_map_invariant_radius (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    {T : E → E} (hT0 : T 0 = 0) (hT : DifferentiableAt ℝ T 0)
    (hcomm : ∀ᶠ z : E in 𝓝 0, F (T z) = T (F z)) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ η →
      ‖P (T (x ξ 0))‖ ≤ r / 2 ∧
      x (P (T (x ξ 0))) = (fun n => T (x ξ n)) := by
  obtain ⟨C, hC, hbound⟩ := hT.isBigO_sub.exists_pos
  have hb : ∀ᶠ z : E in 𝓝 0, ‖T z‖ ≤ C * ‖z‖ := by
    simpa only [hT0, sub_zero] using hbound.bound
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp (hb.and hcomm)
  let η := min (r / 4) (min (s / 4) (r / (4 * C * (‖P‖ + 1))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηr : η ≤ r / 2 := by
    have hh : η ≤ r / 4 := min_le_left _ _
    linarith
  refine ⟨η, hη, hηr, ?_⟩
  intro ξ hξ hξη
  have hξr : ‖ξ‖ ≤ r / 2 := hξη.trans hηr
  have hξs : ‖ξ‖ ≤ s / 4 := hξη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hξC : ‖ξ‖ ≤ r / (4 * C * (‖P‖ + 1)) :=
    hξη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 4 * C * (‖P‖ + 1) * ‖ξ‖ ≤ r := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C * (‖P‖ + 1))).mp hξC
    nlinarith
  have hin (n : ℕ) : x ξ n ∈ ball (0 : E) s := by
    rw [mem_ball, dist_zero_right]
    have hn := h.norm_le ξ hξ hξr n
    have hp := (real_weight_inverse_pow_facts hρ n).2.2.1
    have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 2 * ‖ξ‖)
    nlinarith
  have hyn (n : ℕ) : ‖T (x ξ n)‖ ≤ 2 * C * ‖ξ‖ * (ρ⁻¹) ^ n := by
    calc
      _ ≤ C * ‖x ξ n‖ := (hlocal (hin n)).1
      _ ≤ C * (2 * (ρ⁻¹) ^ n * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left (h.norm_le ξ hξ hξr n) hC.le
      _ = _ := by ring
  have hproj : ‖P (T (x ξ 0))‖ ≤ r / 2 := by
    have hn : ‖T (x ξ 0)‖ ≤ 2 * C * ‖ξ‖ := by
      simpa only [pow_zero, mul_one] using hyn 0
    calc
      _ ≤ ‖P‖ * ‖T (x ξ 0)‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (2 * C * ‖ξ‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg P)
      _ ≤ r / 2 := by nlinarith [norm_nonneg P, norm_nonneg ξ]
  refine ⟨hproj, ?_⟩
  symm
  apply h.unique _ (hP _) hproj
  · intro n
    rw [(hlocal (hin (n + 1))).2, h.backward ξ hξ hξr n]
  · intro n
    have hc : 2 * C * ‖ξ‖ ≤ r := by
      nlinarith [norm_nonneg P, norm_nonneg ξ]
    exact (hyn n).trans (mul_le_mul_of_nonneg_right hc
      (real_weight_inverse_pow_facts hρ n).2.1)
  · rfl

end IsLocalWeightedBackwardGraph

end Euler2D

end
