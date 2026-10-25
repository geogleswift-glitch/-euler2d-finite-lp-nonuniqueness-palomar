module

public import RequestProject.Euler.CircularFixedGraphCaptureBlockBounds
public import RequestProject.Euler.BanachLocalFlatEndpointPerturbation

/-! A genuine endpoint error for a fixed even block of the original
map gives the capture inequalities in the same old graph coordinates.
The graph, norm, isolated flow, and fixed block remain unchanged. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularFixedGraph_forced_capture_block_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lamMult ^ 2) ^ k ∧
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let T := F^[2 * k]
      let A := ((fderiv ℝ F 0) ^ 2) ^ k
      (∀ w, P w = 0 → ‖A w‖ ≤ q * ‖w‖) ∧
      ∃ C > 0, ∃ t > 0, t ≤ r / 2 ∧ ∃ η₀ > 0, ∃ B > 0,
        ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ t →
        let g := fun v => x v 0 - v
        let z := α + g α + w
        ∀ v {η : ℝ}, 0 ≤ η → η ≤ η₀ → ‖v - T z‖ ≤ η →
          ‖P v - (lamMult ^ 2) ^ k • α‖ ≤
            C * (‖α‖ + ‖w‖) ^ 2 + ‖P‖ * η ∧
          ‖(v - P v) - g (P v) - A w‖ ≤
            C * (‖α‖ + ‖w‖) * ‖w‖ + B * η := by
  obtain ⟨k, hk, q, hq, hgap, hcomp, heigen, C, hC, s, hs, hsr, hflat⟩ :=
    exists_circularFixedGraph_capture_block_bounds hγ hγ1 hR hr hX hd hfix harea hg
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let T := F^[2 * k]
  let A := ((fderiv ℝ F 0) ^ 2) ^ k
  let g := fun v => x v 0 - v
  obtain ⟨d, hd₀, _, B, hB, hLip⟩ :=
    circularFixedBackwardGraph_flattening_lipschitz hγ hγ1 hR hr hX hd hfix harea hg
  have hlam : 0 < (lamMult ^ 2) ^ k := pow_pos (pow_pos
    (zero_lt_one.trans one_lt_lamMult) _) _
  have hU (α : CircularConstrainedTangentSpace γ) :
      ‖(lamMult ^ 2) ^ k • α‖ = (lamMult ^ 2) ^ k * ‖α‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have hscalar : ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
      ‖P (T (α + g α + w)) - (lamMult ^ 2) ^ k • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(T (α + g α + w) - P (T (α + g α + w))) -
        g (P (T (α + g α + w))) - A w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
    intro α w hα hw hsize
    have hh := hflat α w hα hw hsize
    have he : A α = (lamMult ^ 2) ^ k • α := by
      have hh' := heigen α
      change A (P α) = (lamMult ^ 2) ^ k • P α at hh'
      rw [hα] at hh'
      exact hh'
    change ‖P (T (α + g α + w)) - A α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(T (α + g α + w) - P (T (α + g α + w))) -
        g (P (T (α + g α + w))) - A w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ at hh
    rw [he] at hh
    exact hh
  obtain ⟨t, ht, hts, η₀, hη₀, hbounds⟩ :=
    local_flattened_bounds_of_endpoint_perturbation T A P g
      (fun α => (lamMult ^ 2) ^ k • α) hlam.le hC hs hd₀ hB hU hLip hscalar
  exact ⟨k, hk, q, hq, hgap, hcomp, C, hC, t, ht, hts.trans hsr,
    η₀, hη₀, B, hB, hbounds⟩

end Euler2D

end
