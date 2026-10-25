module

public import RequestProject.Euler.CircularConstrainedSplitting
public import RequestProject.Euler.CircularPatchMomentResponse
public import RequestProject.Euler.BanachObservableDeparture

/-! The actual strength-weighted fourth patch moment restricted to
the original fourfold fixed-area tangent coordinates. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) constrainedMomentFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) constrainedMomentTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedMomentTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedMomentTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM

def circularConstrainedPatchFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (v : CircularConstrainedTangentSpace γ) : ℂ := circularFamilyPatchFourthMoment hγ hγ1 v.val

theorem circularConstrainedPatchFourthMoment_zero {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    circularConstrainedPatchFourthMoment hγ hγ1 0 = 0 :=
  circularFamilyPatchFourthMoment_zero hγ hγ1

theorem hasFDerivAt_circularConstrainedPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    HasFDerivAt (circularConstrainedPatchFourthMoment hγ hγ1)
      ((fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1) 0).comp
        (circularConstrainedTangentSubmodule γ).subtypeL) 0 := by
  have h := (differentiableAt_circularFamilyPatchFourthMoment_zero hγ hγ1).hasFDerivAt.comp
    (0 : CircularConstrainedTangentSpace γ) (circularConstrainedTangentSubmodule γ).subtypeL.hasFDerivAt
  exact h

theorem fderiv_circularConstrainedPatchFourthMoment_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1.le) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1) = circularPatchGrowingResponse := by
  letI : IsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) :=
    @NormedSpace.toIsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) _ _
      (constrainedMomentTangent_space γ)
  letI : ContinuousSMul ℝ (CircularConstrainedTangentSpace γ) :=
    IsBoundedSMul.continuousSMul
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
    (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) = circularPatchGrowingResponse
  rw [(hasFDerivAt_circularConstrainedPatchFourthMoment_zero hγ hγle).fderiv]
  change fderiv ℝ (circularFamilyPatchFourthMoment hγ hγle) 0
    (circularConstrainedUnstableEmbeddingCLM hγ hγle 1).val = _
  rw [circularConstrainedUnstableEmbeddingCLM_val hγ hγle]
  have hone : circularUnstableEmbeddingCLM hγ hγle 1 = circularGrowingVariation hγ hγ1 0 :=
    circularUnstableEmbeddingCLM_one hγ hγ1
  rw [hone]
  exact fderiv_circularFamilyPatchFourthMoment_growing hγ hγ1

theorem circularConstrainedUnstableEmbedding_ne_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : circularConstrainedUnstableEmbeddingCLM hγ hγ1 1 ≠ 0 := by
  intro hz
  have he := circularConstrainedUnstableCoordinate_embedding hγ hγ1 1
  rw [hz, ContinuousLinearMap.map_zero (circularConstrainedUnstableCoordinateCLM γ)] at he
  exact one_ne_zero he.symm

theorem circularConstrainedUnstableProjection_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    circularConstrainedUnstableProjectionCLM hγ hγ1 (circularConstrainedUnstableEmbeddingCLM hγ hγ1 c) =
      circularConstrainedUnstableEmbeddingCLM hγ hγ1 c := by
  apply Subtype.ext
  simp only [circularConstrainedUnstableProjectionCLM_val, circularConstrainedUnstableEmbeddingCLM_val]
  exact circularUnstableProjectionCLM_embedding hγ hγ1 c

theorem exists_circularConstrainedPatchFourthMoment_departure_cone {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ ε > 0, ∃ r > 0, ∀ (t : ℝ) (v : CircularConstrainedTangentSpace γ), v ∈ ball 0 r →
      ‖v‖ ≤ 2 * |t| * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ →
      ‖v - t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ ≤
        ε * |t| * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ →
      (‖circularPatchGrowingResponse‖ / 2) * |t| ≤
        ‖circularConstrainedPatchFourthMoment hγ hγ1.le v‖ := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  have hφ := hasFDerivAt_circularConstrainedPatchFourthMoment_zero hγ hγle
  have hresponse : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) = circularPatchGrowingResponse :=
    fderiv_circularConstrainedPatchFourthMoment_growing hγ hγ1
  have hg : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) ≠ 0 := by
    rw [hresponse]
    exact circularPatchGrowingResponse_ne_zero
  have h := exists_observable_departure_cone hφ.differentiableAt.hasFDerivAt
    (circularConstrainedUnstableEmbeddingCLM hγ hγle 1) hg
  have hzero : circularConstrainedPatchFourthMoment hγ hγle
      (0 : CircularConstrainedTangentSpace γ) = 0 :=
    circularConstrainedPatchFourthMoment_zero hγ hγle
  simp only [hresponse, hzero, sub_zero] at h
  exact h

end Euler2D

end
