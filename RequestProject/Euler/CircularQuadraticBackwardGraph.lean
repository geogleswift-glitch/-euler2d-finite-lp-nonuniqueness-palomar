module

public import RequestProject.Euler.CircularBackwardGraphTangency
public import RequestProject.Euler.BanachQuadraticBackwardGraph
public import RequestProject.Euler.BanachBackwardGraphOrbitTail

/-! The original circular return graph has the quadratic Lipschitz
estimate needed for flattening. The construction retains the same
actual material flow, and can identify an existing ancient orbit. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) quadraticGraphLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) quadraticGraphLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) quadraticGraphFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) quadraticGraphTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) quadraticGraphTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) quadraticGraphTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) quadraticGraphEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) quadraticGraphTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularConstrained_quadraticBackwardGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
      HasFDerivAt (fun v => x (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0)
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) 0 ∧
      ∃ H > 0,
        (∀ ξ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ r / 2 →
          ∀ ζ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ζ = ζ → ‖ζ‖ ≤ r / 2 →
            ‖(x ξ 0 - ξ) - (x ζ 0 - ζ)‖ ≤ H * (‖ξ‖ + ‖ζ‖) * ‖ξ - ζ‖) ∧
        ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          ‖P (F (x ξ 0))‖ ≤ r / 2 ∧ x (P (F (x ξ 0))) = (fun n => F (x ξ n)) := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hF : ContDiffAt ℝ 2 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 2 hd
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
  have hw : 1 < circularAncientBackwardWeight := by
    have hh := circularAncientBackwardWeight_bounds.1
    linarith
  have hP := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le
  obtain ⟨r, hr, hrr, x, hg, H, hH, hquad⟩ :=
    exists_localWeightedBackwardGraph_quadraticLipschitz_of_kernel_bound
      (E := CircularConstrainedTangentSpace γ) (ρ := circularAncientBackwardWeight)
      (a := lamMult ^ 2) (β := 2) (C := C) (banachDoubleReturn F)
      (contDiffAt_banachDoubleReturn hF0 hF) (banachDoubleReturn_zero hF0) (L ^ 2)
      (fderiv_banachDoubleReturn hF0 (hF.differentiableAt (by norm_num)))
      hw circularAncientBackwardWeight_bounds.2 (by norm_num : (0 : ℝ) ≤ 2)
      circularAncientBackwardWeight_bounds.1 hC.le P hP hcomm heigen hbound hrmax
  have hd1 : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.of_le (by norm_num)
  have hflat := circularConstrainedReturn_hasSharpBackwardOrbits hγ hγ1 hR hX hd1 hfix harea
  exact ⟨r, hr, hrr, x, hg, hg.hasFDerivAt_endpoint hw.le hr hP hflat, H, hH, hquad,
    circularBackwardGraph_singlePeriod_invariance hγ hγ1 hd1 hfix hr hg⟩

theorem exists_actualCircular_quadraticBackwardGraph {γ : ℝ≥0}
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
        ∃ H > 0,
          (∀ ξ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ r / 2 →
            ∀ ζ, circularConstrainedUnstableProjectionCLM hγ hγ1.le ζ = ζ → ‖ζ‖ ≤ r / 2 →
              ‖(x ξ 0 - ξ) - (x ζ 0 - ζ)‖ ≤ H * (‖ξ‖ + ‖ζ‖) * ‖ξ - ζ‖) ∧
          ∃ η > 0, η ≤ r / 2 ∧ ∀ ξ,
            circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
            let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
            let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
            ‖P (F (x ξ 0))‖ ≤ r / 2 ∧ x (P (F (x ξ 0))) = (fun n => F (x ξ n)) := by
  obtain ⟨R, hR, X, hX, hs, hfix, _, harea, _⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hd3 : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have ha := fun W hW i => harea W hW period hp i
  refine ⟨R, hR, X, hX, hd3, hfix, ha, ?_⟩
  exact exists_circularConstrained_quadraticBackwardGraph hγ hγ1 hR hX
    (hd3.of_le (by norm_num)) hfix ha hrmax

end Euler2D

end
