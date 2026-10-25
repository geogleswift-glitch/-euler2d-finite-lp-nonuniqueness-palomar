module

public import RequestProject.Euler.CircularQuadraticBackwardGraph
public import RequestProject.Euler.BanachFixedPointIterates
public import RequestProject.Euler.CaptureBlockPowerGap
public import RequestProject.Euler.BanachCaptureLinearBlock

/-! A fixed even iterate of the same actual return map has the spectral
gap needed by capture in the original norm. The same old weighted graph
is genuinely invariant under this iterate. The block is chosen before
any physical scale, layer ratio, or truncation. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) captureBlockLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) captureBlockLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) captureBlockFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) captureBlockTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
      Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) captureBlockTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
      Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) captureBlockTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) captureBlockEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) captureBlockTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularConstrained_capture_linear_block {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i)) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lamMult ^ 2) ^ k ∧
      let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let T := F^[2 * k]
      let A := ((fderiv ℝ F 0) ^ 2) ^ k
      ContDiffAt ℝ 2 T 0 ∧ T 0 = 0 ∧ HasFDerivAt T A 0 ∧
      (∀ v, P v = 0 → ‖A v‖ ≤ q * ‖v‖) ∧
      (∀ v, A (P v) = (lamMult ^ 2) ^ k • P v) ∧
      ∀ {r : ℝ}, 0 < r →
        ∀ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
          IsLocalWeightedBackwardGraph (banachDoubleReturn F) P circularAncientBackwardWeight r x →
          ∃ η > 0, η ≤ r / 2 ∧ ∀ α, P α = α → ‖α‖ ≤ η →
            ‖P (T (x α 0))‖ ≤ r / 2 ∧ x (P (T (x α 0))) = (fun n => T (x α n)) := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : ContDiffAt ℝ 2 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 2 hd
  have hfd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.differentiableAt (by norm_num)
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_circularConstrainedDoubleDerivative_complement_power_le hγ hγ1 hR hX hfd hfix harea
  have heigen (v : CircularConstrainedTangentSpace γ) :
      (L ^ 2) (P v) = lamMult ^ 2 • P v :=
    circularConstrainedDoubleDerivative_projection_eigen hγ hγ1 hR hX hfd hfix harea v
  obtain ⟨k, hk, q, hq, hgap, hqbound, heigenk⟩ :=
    exists_banach_capture_linear_block L P two_lt_lamMult heigen hbound
  have hderiv : HasFDerivAt F^[2 * k] ((L ^ 2) ^ k) 0 := by
    simpa only [pow_mul] using
      hasFDerivAt_iterate_zero hF0 (hF.differentiableAt (by norm_num)).hasFDerivAt (2 * k)
  refine ⟨k, hk, q, hq, hgap, ?_⟩
  dsimp only
  refine ⟨contDiffAt_iterate_zero hF0 hF _, iterate_zero_of_map_zero hF0 _, hderiv, ?_, ?_, ?_⟩
  · intro v hv
    exact hqbound v hv
  · intro v
    exact heigenk v
  · intro r hr x hg
    have hw : 1 ≤ circularAncientBackwardWeight := by
      have hh := circularAncientBackwardWeight_bounds.1
      linarith
    exact hg.exists_iterate_invariant_radius hw hr
      (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) hF0 (hF.of_le (by norm_num)) _

end Euler2D

end
