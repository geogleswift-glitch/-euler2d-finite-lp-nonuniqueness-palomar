module

public import RequestProject.Euler.CircularBackwardGraphInvariance
public import RequestProject.Euler.BanachBackwardGraphTangency
public import RequestProject.Euler.BanachBackwardGraphCommutingInvariance

/-! A single actual circular graph has its true unstable tangent and
a common neighborhood on which the original double return preserves
it in both directions. Full C³ graph regularity is not asserted. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) tangentGraphLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) tangentGraphLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) tangentGraphFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) tangentGraphTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) tangentGraphTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) tangentGraphTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) tangentGraphEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) tangentGraphTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_actualCircular_tangent_invariant_backwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ R > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) R) period X ∧
      ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
        littleContourArea γ (X W period i) = littleContourArea γ (W i)) ∧
      ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
        IsLocalWeightedBackwardGraph
          (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
          (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
        HasFDerivAt (fun v => x (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0)
          (circularConstrainedUnstableProjectionCLM hγ hγ1.le) 0 ∧
        ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
          ‖P (x ξ 1)‖ ≤ r / 2 ∧ ‖P (F (x ξ 0))‖ ≤ r / 2 ∧
          x (P (x ξ 1)) = (fun n => x ξ (n + 1)) ∧
          x (P (F (x ξ 0))) = (fun n => Nat.casesOn n (F (x ξ 0)) (fun k => x ξ k)) := by
  obtain ⟨R, hR, X, hX, hd3, hfix, harea, r, hr, hrr, x, hg, _⟩ :=
    exists_actualCircular_localBackwardGraph hγ hγ1 (by norm_num : (0 : ℝ) < 1) hrmax
  have hd1 : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd3.of_le (by norm_num)
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : ContDiffAt ℝ 1 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd1
  have hflat := circularConstrainedReturn_hasSharpBackwardOrbits hγ hγ1 hR hX hd1 hfix harea
  have hw : 1 ≤ circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  have hP := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le
  refine ⟨R, hR, X, hX, hd3, hfix, harea, r, hr, hrr, x, hg, ?_, ?_⟩
  · exact hg.hasFDerivAt_endpoint hw hr hP hflat
  · exact hg.exists_twoSided_invariant_radius hw hr hP (banachDoubleReturn_zero hF0)
      (contDiffAt_banachDoubleReturn hF0 hF).continuousAt

theorem circularBackwardGraph_singlePeriod_invariance {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hd : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    {r : ℝ} (hr : 0 < r)
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      ‖P (F (x ξ 0))‖ ≤ r / 2 ∧ x (P (F (x ξ 0))) = (fun n => F (x ξ n)) := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : DifferentiableAt ℝ F 0 :=
    (contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd).differentiableAt (by norm_num)
  have hw : 1 ≤ circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  exact hg.exists_commuting_map_invariant_radius hw hr
    (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) hF0 hF
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem exists_actualCircular_singlePeriod_invariant_backwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ R > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) R) period X ∧
      ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
        littleContourArea γ (X W period i) = littleContourArea γ (W i)) ∧
      ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
        IsLocalWeightedBackwardGraph
          (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
          (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
        HasFDerivAt (fun v => x (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0)
          (circularConstrainedUnstableProjectionCLM hγ hγ1.le) 0 ∧
        ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          ‖P (F (x ξ 0))‖ ≤ r / 2 ∧ x (P (F (x ξ 0))) = (fun n => F (x ξ n)) := by
  obtain ⟨R, hR, X, hX, hd3, hfix, harea, r, hr, hrr, x, hg, hder, _⟩ :=
    exists_actualCircular_tangent_invariant_backwardGraph hγ hγ1 hrmax
  refine ⟨R, hR, X, hX, hd3, hfix, harea, r, hr, hrr, x, hg, hder, ?_⟩
  exact circularBackwardGraph_singlePeriod_invariance hγ hγ1
    (hd3.of_le (by norm_num)) hfix hr hg

end Euler2D

end
