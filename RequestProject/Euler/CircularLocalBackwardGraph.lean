module

public import RequestProject.Euler.CircularDoubleReturnSplitting
public import RequestProject.Euler.CircularConstrainedPeriodMap
public import RequestProject.Euler.BanachLocalBackwardGraph

/-! The weighted graph is instantiated for the actual fixed-area,
fourfold circular return map. The full-period material flow and all
splitting estimates are the previously constructed original ones. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) localGraphLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) localGraphLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) localGraphFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) localGraphTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) localGraphTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) localGraphTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) localGraphEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) localGraphTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularConstrained_localBackwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {w ε rmax : ℝ} (hw : 2 < w) (hwa : w < lamMult ^ 2)
    (hε : 0 < ε) (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x ∧
      ∀ ξ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ r / 2 →
        ‖x ξ 0 - ξ‖ ≤ ε * ‖ξ‖ := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hF : ContDiffAt ℝ 1 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hfd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.differentiableAt (by norm_num)
  have hcomm : (L ^ 2).comp P = P.comp (L ^ 2) :=
    circularConstrainedDoubleDerivative_projection_commute hγ hγ1 hR hX hfd hfix harea
  have heigen (v : CircularConstrainedTangentSpace γ) :
      (L ^ 2) (P v) = lamMult ^ 2 • P v :=
    circularConstrainedDoubleDerivative_projection_eigen hγ hγ1 hR hX hfd hfix harea v
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_circularConstrainedDoubleDerivative_complement_power_le hγ hγ1 hR hX hfd hfix harea
  exact exists_localWeightedBackwardGraph_of_kernel_bound
    (E := CircularConstrainedTangentSpace γ) (ρ := w) (a := lamMult ^ 2) (β := 2) (C := C)
    (banachDoubleReturn F) (contDiffAt_banachDoubleReturn hF0 hF)
    (banachDoubleReturn_zero hF0) (L ^ 2)
    (fderiv_banachDoubleReturn hF0 (hF.differentiableAt (by norm_num)))
    (by linarith : 1 < w) hwa (by norm_num : (0 : ℝ) ≤ 2) hw hC.le P
    (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) hcomm heigen hbound hε hrmax

theorem exists_actualCircular_localBackwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ε rmax : ℝ} (hε : 0 < ε) (hrmax : 0 < rmax) :
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
        ∀ ξ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ r / 2 →
          ‖x ξ 0 - ξ‖ ≤ ε * ‖ξ‖ := by
  obtain ⟨R, hR, X, hX, hs, hfix, _, harea, _⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hd3 : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have ha := fun W hW i => harea W hW period hp i
  refine ⟨R, hR, X, hX, hd3, hfix, ha, ?_⟩
  exact exists_circularConstrained_localBackwardGraph hγ hγ1 hR hX
    (hd3.of_le (by norm_num)) hfix ha circularAncientBackwardWeight_bounds.1
    circularAncientBackwardWeight_bounds.2 hε hrmax

end Euler2D

end
