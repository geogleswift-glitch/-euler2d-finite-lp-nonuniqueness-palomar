module

public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.CircularPatchMomentResponse
public import RequestProject.Euler.BanachObservableDeparture

/-! The actual strength-weighted fourth patch moment restricted to
the original fourfold fixed-area tangent coordinates. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) linearMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) linearMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) linearMomentFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) linearMomentTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) linearMomentTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) linearMomentTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM

theorem circularAreaChartFourthMoment_mode_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    HasDerivAt (fun s : ℝ => circularAreaChartFourthMoment hγ hγ1 i
      (s • circularNormalModeLittle hγ hγ1 2 η τ i))
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) 0 := by
  have hs : HasDerivAt (fun s : ℝ => s • circularNormalModeLittle hγ hγ1 2 η τ i)
      (circularNormalModeLittle hγ hγ1 2 η τ i) 0 := by
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularNormalModeLittle hγ hγ1 2 η τ i)
  have hchart : HasFDerivAt (littleAreaChart hγ hγ1 (circularContourRadii i))
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ))
      ((fun s : ℝ => s • circularNormalModeLittle hγ hγ1 2 η τ i) 0) := by
    simpa only [zero_smul] using hasFDerivAt_littleAreaChart_zero hγ hγ1 (circularContourRadii i)
  apply hasDerivAt_littlePatchFourthMoment_of_boundary hγ hγ1 (growingMoment_radius_pos i)
  · exact (hchart.comp_hasDerivAt 0 hs).continuousAt
  · simp only [zero_smul, littleAreaChart_zero]
  · exact hasDerivAt_littleAreaChart_fourthMoment hγ hγ1 η τ i

theorem circularFamilyPatchFourthMoment_mode_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) :
    HasDerivAt (fun s : ℝ => circularFamilyPatchFourthMoment hγ hγ1
      (s • circularNormalModeLittle hγ hγ1 2 η τ))
      (∑ i : Fin 2, (circularContourStrengths i : ℂ) *
        (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i)) 0 := by
  have h0 := (circularAreaChartFourthMoment_mode_hasDerivAt hγ hγ1 η τ 0).const_mul
    (circularContourStrengths 0 : ℂ)
  have h1 := (circularAreaChartFourthMoment_mode_hasDerivAt hγ hγ1 η τ 1).const_mul
    (circularContourStrengths 1 : ℂ)
  convert h0.add h1 using 1
  · funext s
    simp only [circularFamilyPatchFourthMoment, Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply]
  · simp only [Fin.sum_univ_two]

theorem fderiv_circularFamilyPatchFourthMoment_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) :
    fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1) 0 (circularNormalModeLittle hγ hγ1 2 η τ) =
      ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
        (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) := by
  have hs : HasDerivAt (fun s : ℝ => s • circularNormalModeLittle hγ hγ1 2 η τ)
      (circularNormalModeLittle hγ hγ1 2 η τ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [Pi.smul_apply, id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularNormalModeLittle hγ hγ1 2 η τ i)
  have hd : HasFDerivAt (circularFamilyPatchFourthMoment hγ hγ1)
      (fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1) 0)
      ((fun s : ℝ => s • circularNormalModeLittle hγ hγ1 2 η τ) 0) := by
    simpa only [zero_smul] using (differentiableAt_circularFamilyPatchFourthMoment_zero hγ hγ1).hasFDerivAt
  have hc := hd.comp_hasDerivAt (0 : ℝ) hs
  exact hc.unique (circularFamilyPatchFourthMoment_mode_hasDerivAt hγ hγ1 η τ)

theorem fderiv_circularFamilyPatchFourthMoment_unstableEmbedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) :
    fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1.le) 0
      (circularUnstableEmbeddingCLM hγ hγ1.le c) = circularPatchGrowingResponse * c := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularFamilyPatchFourthMoment hγ hγle) 0
    (circularUnstableEmbeddingCLM hγ hγle c) = circularPatchGrowingResponse * c
  rw [circularUnstableEmbeddingCLM_apply hγ hγle c,
    fderiv_circularFamilyPatchFourthMoment_normalMode hγ hγle]
  simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  norm_num [circularContourStrengths, circularContourRadii, vPlus, circularPatchGrowingResponse]
  ring

theorem fderiv_circularConstrainedPatchFourthMoment_unstableEmbedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) :
    fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1.le) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c) = circularPatchGrowingResponse * c := by
  letI : IsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) :=
    @NormedSpace.toIsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) _ _
      (linearMomentTangent_space γ)
  letI : ContinuousSMul ℝ (CircularConstrainedTangentSpace γ) :=
    IsBoundedSMul.continuousSMul
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
    (circularConstrainedUnstableEmbeddingCLM hγ hγle c) = circularPatchGrowingResponse * c
  rw [(hasFDerivAt_circularConstrainedPatchFourthMoment_zero hγ hγle).fderiv]
  change fderiv ℝ (circularFamilyPatchFourthMoment hγ hγle) 0
    (circularConstrainedUnstableEmbeddingCLM hγ hγle c).val = _
  rw [circularConstrainedUnstableEmbeddingCLM_val hγ hγle c]
  exact fderiv_circularFamilyPatchFourthMoment_unstableEmbedding hγ hγ1 c

theorem fderiv_circularConstrainedPatchFourthMoment_ne_zero_on_unstable {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ)
    (hv : circularConstrainedUnstableProjectionCLM hγ hγ1.le v = v) (hv0 : v ≠ 0) :
    fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγ1.le) 0 v ≠ 0 := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0 v ≠ 0
  have he : v = circularConstrainedUnstableEmbeddingCLM hγ hγle
      (circularConstrainedUnstableCoordinateCLM γ v) := by
    calc
      v = circularConstrainedUnstableProjectionCLM hγ hγle v := hv.symm
      _ = _ := by unfold circularConstrainedUnstableProjectionCLM; rfl
  have hcoord : circularConstrainedUnstableCoordinateCLM γ v ≠ 0 := by
    intro hz
    apply hv0
    rw [he, hz, ContinuousLinearMap.map_zero (circularConstrainedUnstableEmbeddingCLM hγ hγle)]
  have hresponse : fderiv ℝ (circularConstrainedPatchFourthMoment hγ hγle) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγle (circularConstrainedUnstableCoordinateCLM γ v)) =
    circularPatchGrowingResponse * circularConstrainedUnstableCoordinateCLM γ v :=
    fderiv_circularConstrainedPatchFourthMoment_unstableEmbedding hγ hγ1 _
  rw [he, hresponse]
  exact mul_ne_zero circularPatchGrowingResponse_ne_zero hcoord

end Euler2D

end
