module

public import RequestProject.Euler.BanachLocalBackwardGraph
public import RequestProject.Euler.BanachBackwardOrbitDeparture

/-! Uniqueness identifies all smaller contraction constructions with
one common graph. Thus their arbitrarily small cone errors prove a
genuine Fréchet tangent at the fixed point for that same graph. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsLocalWeightedBackwardGraph

variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem eventually_endpoint_error_le (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hflat : HasFlatBackwardOrbits F P ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s > 0, s ≤ r ∧ ∀ ξ, P ξ = ξ → ‖ξ‖ ≤ s / 2 →
      ‖x ξ 0 - ξ‖ ≤ ε * ‖ξ‖ := by
  obtain ⟨s, hs, hsr, hex⟩ := hflat ε hε r hr
  refine ⟨s, hs, hsr, ?_⟩
  intro ξ hξ hξs
  have hξr : ‖ξ‖ ≤ r / 2 := hξs.trans (by linarith)
  obtain ⟨y, hyrec, _, hynorm, hyproj, hyerror, _⟩ := hex ξ hξ hξs
  have hybound (n : ℕ) : ‖y n‖ ≤ r * (ρ⁻¹) ^ n := by
    have hp := (real_weight_inverse_pow_facts hρ n).2.1
    have hh := mul_le_mul_of_nonneg_right hξr hp
    have hn := hynorm n
    nlinarith
  have hy : y = x ξ := h.unique ξ hξ hξr y hyrec hybound hyproj
  simpa only [hy] using hyerror

theorem hasFDerivAt_endpoint (h : IsLocalWeightedBackwardGraph F P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (hflat : HasFlatBackwardOrbits F P ρ) :
    HasFDerivAt (fun v : E => x (P v) 0) P 0 := by
  have hx0 : x 0 0 = 0 := congrArg (fun y : ℕ → E => y 0) (h.zero hr.le)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let e := ε / (‖P‖ + 1)
  have he : 0 < e := div_pos hε (by positivity)
  obtain ⟨s, hs, _, hsmall⟩ := h.eventually_endpoint_error_le hρ hr hflat he
  have hlim : Tendsto (fun v : E => ‖P v‖) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero, norm_zero] using (P.continuous.tendsto (0 : E)).norm
  filter_upwards [hlim.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < s / 2))]
    with v hv
  simp only [zero_add, map_zero, hx0, sub_zero]
  calc
    _ ≤ e * ‖P v‖ := hsmall (P v) (hP v) hv.le
    _ ≤ e * (‖P‖ * ‖v‖) := mul_le_mul_of_nonneg_left (P.le_opNorm v) he.le
    _ ≤ ε * ‖v‖ := by
      have hh : e * (‖P‖ + 1) = ε := by
        dsimp only [e]
        field_simp
      have hc : e * ‖P‖ ≤ ε := by nlinarith
      nlinarith [norm_nonneg v]

end IsLocalWeightedBackwardGraph

end Euler2D

end
