module

public import RequestProject.Euler.CircularInnerMomentDetector
public import RequestProject.Euler.CircularFixedGraphQuadraticBound

/-! A genuine capture section with its actual small graph error has a
uniformly nonzero inner patch moment, for every complex growing phase.
The capture radius is selected before the later graph error coefficient. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] innerDetectorLittle_group innerDetectorLittle_space
  innerDetectorFamily_tower innerDetectorTangent_group innerDetectorTangent_space
  innerDetectorTangent_continuousAdd fixedGraphTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

theorem exists_fixedGraph_innerMoment_capture_section {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Rflow r₀ : ℝ} (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq) :
    ∃ δmax > 0, ∃ m > 0, ∀ δ : ℝ, 0 < δ → δ < δmax →
      ∀ Cgraph : ℝ, 0 ≤ Cgraph → ∀ᶠ ξ : ℝ in atTop,
      ∀ v : CircularConstrainedTangentSpace γ,
        let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
        ‖α‖ = δ → ‖v - gseq α 0‖ ≤ Cgraph * Real.exp (-ξ) ^ 3 →
        ‖v‖ ≤ 3 * δ ∧ (m / 2) * δ ≤ ‖circularConstrainedInnerPatchFourthMoment hγ hγ1.le v‖ := by
  obtain ⟨m, hm, ε, hε, hεOne, r, hr, hdetector⟩ :=
    exists_circularConstrainedInnerPatchFourthMoment_uniform_cone hγ hγ1
  obtain ⟨d, hdpos, hdr₀, H, hH, hquad⟩ :=
    circularFixedBackwardGraph_quadratic_difference hγ hγ1 hRflow hr₀ hflow hd hfix harea hg
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hgzero : gseq (0 : CircularConstrainedTangentSpace γ) 0 = 0 := by
    have hnorm : ‖gseq (0 : CircularConstrainedTangentSpace γ) 0‖ ≤ 0 := by
      simpa only [norm_zero, pow_zero, mul_one, mul_zero] using
        hg.norm_le 0 (map_zero Q) (by simpa only [norm_zero] using (half_pos hr₀).le) 0
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  let δmax := min d (min (r / 4) (ε / (2 * H)))
  have hδmax : 0 < δmax := lt_min hdpos (lt_min (by positivity) (by positivity))
  refine ⟨δmax, hδmax, m, hm, ?_⟩
  intro δ hδ hδbound Cgraph hCgraph
  have hδd : δ ≤ d := hδbound.le.trans (min_le_left _ _)
  have hδr : δ < r / 4 := hδbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ ≤ ε / (2 * H) := hδbound.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hHδ : H * δ ≤ ε / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hH)).mp hδε
    linarith only [hh]
  have ht : Tendsto (fun ξ : ℝ => Cgraph * Real.exp (-ξ) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 3).const_mul Cgraph
  filter_upwards [ht.eventually (gt_mem_nhds (mul_pos (half_pos hε) hδ))] with ξ hsmall
  intro v
  dsimp only
  intro hαnorm herror
  let α := Q v
  have hαnorm' : ‖α‖ = δ := hαnorm
  have hα : Q α = α := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le v
  have hαd : ‖α‖ ≤ d := by rw [hαnorm]; exact hδd
  have hgraph : ‖gseq α 0‖ ≤ 2 * δ := by
    simpa only [pow_zero, mul_one, hαnorm'] using hg.norm_le α hα (hαd.trans hdr₀) 0
  have hquadAt : ‖gseq α 0 - α‖ ≤ (ε / 2) * δ := by
    have hh := hquad α hα hαd 0 (map_zero Q) (by simpa only [norm_zero] using hdpos.le)
    have hquadratic : ‖gseq α 0 - α‖ ≤ H * δ ^ 2 := by
      simpa only [hgzero, norm_zero, sub_zero, add_zero, hαnorm', pow_two, mul_assoc] using hh
    exact hquadratic.trans (by
      calc
        _ = (H * δ) * δ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hHδ hδ.le)
  have herrorSmall : ‖v - gseq α 0‖ ≤ (ε / 2) * δ := herror.trans hsmall.le
  have hnorm : ‖v‖ ≤ 3 * δ := by
    have htriangle := norm_add_le (v - gseq α 0) (gseq α 0)
    rw [sub_add_cancel] at htriangle
    have he := mul_le_mul_of_nonneg_right hεOne hδ.le
    linarith only [htriangle, herrorSmall, hgraph, he, hδ.le]
  have hv : v ∈ ball 0 r := by
    apply mem_ball_zero_iff.mpr
    linarith only [hnorm, hδr, hδ.le]
  have hcone : ‖v - α‖ ≤ ε * ‖α‖ := by
    have hid : v - α = (v - gseq α 0) + (gseq α 0 - α) := (sub_add_sub_cancel v (gseq α 0) α).symm
    rw [hid, hαnorm]
    exact (norm_add_le _ _).trans (by linarith only [herrorSmall, hquadAt])
  refine ⟨hnorm, ?_⟩
  simpa only [hαnorm] using hdetector v hv hcone

end Euler2D

end
