module

public import RequestProject.Euler.CircularDoubleReturnSplitting
public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.BanachNonzeroOrbitAsymptotic
public import RequestProject.Euler.CircularHyperbolicGap
public import RequestProject.Euler.BanachDoubleReturn
public import RequestProject.Euler.BanachNonlinearKernelOrbit

/-! Genuine nonlinear ancient discrete orbits of the original
fourfold fixed-area return map. The full original Banach power bound,
actual unstable projection, and true derivative are used directly. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) sharpAsymptoticLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sharpAsymptoticLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sharpAsymptoticFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) sharpAsymptoticTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpAsymptoticTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpAsymptoticTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) sharpAsymptoticEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) sharpAsymptoticTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM circularConstrainedPatchFourthMoment

theorem exists_circularConstrained_nonzero_asymptotic_orbit {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : ℕ → CircularConstrainedTangentSpace γ,
    ∃ c : CircularConstrainedTangentSpace γ, ∃ B > 0,
      (∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
        (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 rmax) ∧
      (∀ n, ‖x n‖ ≤ 2 * circularAncientBackwardRatio ^ n *
        ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le (x 0) =
        t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1 ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le c = c ∧ c ≠ 0 ∧
      (∀ n : ℕ, ‖x n - ((lamMult ^ 2)⁻¹) ^ n • c‖ ≤ B * (circularAncientBackwardRatio ^ 2) ^ n) ∧
      circularConstrainedPatchFourthMoment hγ hγ1.le (x 0) ≠ 0 ∧ Tendsto x atTop (𝓝 0) := by
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let D := L ^ 2
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hF2 : ContDiffAt ℝ 2 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 2 hd
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hfd := hd.differentiableAt (by norm_num)
  have hD : fderiv ℝ (banachDoubleReturn F) 0 = D :=
    fderiv_banachDoubleReturn hF0 (hF2.differentiableAt (by norm_num))
  have hcomm : D.comp P = P.comp D :=
    circularConstrainedDoubleDerivative_projection_commute hγ hγ1 hR hX hfd hfix harea
  have heigen (v : CircularConstrainedTangentSpace γ) : D (P v) = lamMult ^ 2 • P v :=
    circularConstrainedDoubleDerivative_projection_eigen hγ hγ1 hR hX hfd hfix harea v
  obtain ⟨M, hM, hbound⟩ :=
    exists_norm_circularConstrainedDoubleDerivative_complement_power_le hγ hγ1 hR hX hfd hfix harea
  have horbit := circularConstrainedReturn_hasSharpBackwardOrbits hγ hγ1 hR hX
    (hd.of_le (by norm_num)) hfix harea
  have hφ := (hasFDerivAt_circularConstrainedPatchFourthMoment_zero hγ hγ1.le).differentiableAt.hasFDerivAt
  have hg : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1.le) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1) ≠ 0 := by
    rw [fderiv_circularConstrainedPatchFourthMoment_growing hγ hγ1]
    exact circularPatchGrowingResponse_ne_zero
  have h := exists_backwardOrbit_nonzero_asymptotic (E := CircularConstrainedTangentSpace γ)
    (F := banachDoubleReturn F) (w := circularAncientBackwardWeight) (a := lamMult ^ 2) (M := M) (β := 2)
    (contDiffAt_banachDoubleReturn hF0 hF2) (banachDoubleReturn_zero hF0) D P hD
    (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) hcomm
    (by linarith [circularAncientBackwardWeight_bounds.1] : (1 : ℝ) < circularAncientBackwardWeight)
    (by nlinarith [four_lt_lamMult_sq] : 0 < lamMult ^ 2) hM.le (by norm_num : (0 : ℝ) ≤ 2)
    (by rw [circularAncientBackwardWeight_inv]; exact circularAncientBackwardRatio_unstable_quadratic_gap)
    (by rw [circularAncientBackwardWeight_inv]; exact circularAncientBackwardRatio_stable_gaps.1)
    (by rw [circularAncientBackwardWeight_inv]; exact circularAncientBackwardRatio_stable_gaps.2)
    heigen hbound horbit hφ (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1)
    (circularConstrainedUnstableProjection_embedding hγ hγ1.le 1) hg hrmax
  simpa only [circularAncientBackwardWeight_inv, circularConstrainedPatchFourthMoment_zero] using h

end Euler2D

end
