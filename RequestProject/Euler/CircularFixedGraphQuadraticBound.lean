module

public import RequestProject.Euler.CircularQuadraticBackwardGraph
public import RequestProject.Euler.BanachBackwardGraphCommonGerm
public import RequestProject.Euler.BanachFlattenedForcingError

/-! The graph already fixed together with the actual ancient orbit
inherits the quadratic Lipschitz estimate from the real contraction
construction for the same return map. No new ancient orbit is chosen. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) fixedGraphLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fixedGraphLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) fixedGraphFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) fixedGraphTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) fixedGraphTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) fixedGraphTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) fixedGraphTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem circularFixedBackwardGraph_quadratic_difference {γ : ℝ≥0}
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
    ∃ d > 0, d ≤ r / 2 ∧ ∃ H > 0, ∀ α,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α → ‖α‖ ≤ d → ∀ β,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le β = β → ‖β‖ ≤ d →
      ‖(x α 0 - α) - (x β 0 - β)‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖ := by
  obtain ⟨s, hs, hsr, y, hy, _, H, hH, hquad, _⟩ :=
    exists_circularConstrained_quadraticBackwardGraph hγ hγ1 hR hX hd hfix harea hr
  have hρ : 0 ≤ circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  refine ⟨s / 2, by positivity, div_le_div_of_nonneg_right hsr (by norm_num), H, hH, ?_⟩
  intro α hα hαd β hβ hβd
  apply hg.quadratic_difference_of_comparisonGraph hy hρ hquad hα _ hβ _
  · simpa only [min_eq_right hsr] using hαd
  · simpa only [min_eq_right hsr] using hβd

theorem circularFixedBackwardGraph_flattening_lipschitz {γ : ℝ≥0}
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
    ∃ d > 0, d ≤ r / 2 ∧ ∃ B > 0, ∀ u v,
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le u‖ ≤ d →
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le v‖ ≤ d →
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun α => x α 0 - α
      ‖(v - P v - g (P v)) - (u - P u - g (P u))‖ ≤ B * ‖v - u‖ := by
  obtain ⟨d, hd₀, hdr, H, hH, hquad⟩ :=
    circularFixedBackwardGraph_quadratic_difference hγ hγ1 hR hr hX hd hfix harea hg
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  refine ⟨d, hd₀, hdr, 1 + ‖P‖ + H * (2 * d) * ‖P‖, by positivity, ?_⟩
  intro u v hu hv
  apply norm_flattenedCoordinate_sub_le P (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le)
    (fun α => x α 0 - α) (by positivity) hH.le
    (fun α hα hαd β hβ hβd => hquad α hα (by linarith) β hβ (by linarith)) u v
  · linarith
  · linarith

end Euler2D

end
