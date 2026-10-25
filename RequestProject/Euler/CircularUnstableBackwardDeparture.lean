module

public import RequestProject.Euler.CircularConstrainedBackwardOrbit
public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.BanachBackwardOrbitDeparture

/-! Ancient discrete orbits of the genuine constrained return map
whose actual strength-weighted fourth patch moment is strictly nonzero. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) departureLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) departureLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) departureFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) departureTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) departureTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) departureTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) departureTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM circularConstrainedPatchFourthMoment

theorem exists_circularConstrained_backward_departure {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ t > 0, ∃ x : ℕ → CircularConstrainedTangentSpace γ,
      (∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
        (x (n + 1)) = x n) ∧
      (∀ n, x n ∈ closedBall 0 rmax) ∧
      (∀ n, ‖x n‖ ≤ 2 * ((3 : ℝ)⁻¹) ^ n *
        ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le (x 0) =
        t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1 ∧
      (‖circularPatchGrowingResponse‖ / 2) * t ≤
        ‖circularConstrainedPatchFourthMoment hγ hγ1.le (x 0)‖ ∧
      circularConstrainedPatchFourthMoment hγ hγ1.le (x 0) ≠ 0 ∧ Tendsto x atTop (𝓝 0) := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  have horbit : HasFlatBackwardOrbits
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγle) 3 := by
    intro ε hε radius hradius
    exact exists_circularConstrained_backward_orbit hγ hγ1 hR hX hd hfix harea hε hradius
  have hφ := (hasFDerivAt_circularConstrainedPatchFourthMoment_zero hγ hγle).differentiableAt.hasFDerivAt
  have hresponse : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) = circularPatchGrowingResponse :=
    fderiv_circularConstrainedPatchFourthMoment_growing hγ hγ1
  have hg : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) ≠ 0 := by
    rw [hresponse]
    exact circularPatchGrowingResponse_ne_zero
  have h := exists_backwardOrbit_with_observable_departure horbit hφ
    (circularConstrainedUnstableEmbeddingCLM hγ hγle 1)
    (circularConstrainedUnstableProjection_embedding hγ hγle 1) hg hrmax
  have hzero : circularConstrainedPatchFourthMoment hγ hγle
      (0 : CircularConstrainedTangentSpace γ) = 0 :=
    circularConstrainedPatchFourthMoment_zero hγ hγle
  simp only [hresponse, hzero, sub_zero] at h
  exact h

end Euler2D

end
