module

public import RequestProject.Euler.BanachObservableSubspaceCone
public import RequestProject.Euler.CircularPatchMomentUnstableLinear

public import RequestProject.Euler.CircularConstrainedPatchMoment
public import RequestProject.Euler.CircularPatchMomentResponse
public import RequestProject.Euler.BanachObservableDeparture

/-! The actual strength-weighted fourth patch moment restricted to
the original fourfold fixed-area tangent coordinates. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) innerDetectorLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) innerDetectorLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) innerDetectorFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) innerDetectorTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) innerDetectorTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) innerDetectorTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM


def circularConstrainedInnerPatchFourthMoment {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (v : CircularConstrainedTangentSpace γ) : ℂ :=
  circularAreaChartFourthMoment hγ hγ1 0 (v.val 0)

theorem circularConstrainedInnerPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : circularConstrainedInnerPatchFourthMoment hγ hγ1 0 = 0 :=
  circularAreaChartFourthMoment_zero hγ hγ1 0

theorem hasFDerivAt_circularConstrainedInnerPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    HasFDerivAt (circularConstrainedInnerPatchFourthMoment hγ hγ1)
      ((fderiv ℝ (circularAreaChartFourthMoment hγ hγ1 0) 0).comp
        ((ContinuousLinearMap.proj (0 : Fin 2)).comp (circularConstrainedTangentSubmodule γ).subtypeL)) 0 := by
  let L : CircularConstrainedTangentSpace γ →L[ℝ] LittleContourSpace γ :=
    (ContinuousLinearMap.proj (0 : Fin 2)).comp (circularConstrainedTangentSubmodule γ).subtypeL
  have hd : HasFDerivAt (circularAreaChartFourthMoment hγ hγ1 0)
      (fderiv ℝ (circularAreaChartFourthMoment hγ hγ1 0) 0) (L 0) := by
    simpa only [ContinuousLinearMap.map_zero L] using
      (differentiableAt_circularAreaChartFourthMoment_zero hγ hγ1 0).hasFDerivAt
  exact hd.comp 0 L.hasFDerivAt

theorem fderiv_circularAreaChartFourthMoment_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    fderiv ℝ (circularAreaChartFourthMoment hγ hγ1 i) 0
      (circularNormalModeLittle hγ hγ1 2 η τ i) =
      (Real.pi : ℂ) * (circularContourRadii i : ℂ) ^ 6 * η i := by
  let g := circularNormalModeLittle hγ hγ1 2 η τ i
  have hs : HasDerivAt (fun s : ℝ => s • g) g 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const g
  have hd : HasFDerivAt (circularAreaChartFourthMoment hγ hγ1 i)
      (fderiv ℝ (circularAreaChartFourthMoment hγ hγ1 i) 0) ((fun s : ℝ => s • g) 0) := by
    simpa only [zero_smul] using (differentiableAt_circularAreaChartFourthMoment_zero hγ hγ1 i).hasFDerivAt
  have hc := hd.comp_hasDerivAt 0 hs
  change HasDerivAt (fun s : ℝ => circularAreaChartFourthMoment hγ hγ1 i (s • g))
    (fderiv ℝ (circularAreaChartFourthMoment hγ hγ1 i) 0 g) 0 at hc
  exact hc.unique (circularAreaChartFourthMoment_mode_hasDerivAt hγ hγ1 η τ i)

theorem fderiv_circularConstrainedInnerPatchFourthMoment_unstableEmbedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) :
    fderiv ℝ (circularConstrainedInnerPatchFourthMoment hγ hγ1.le) 0
      (circularConstrainedUnstableEmbeddingCLM hγ hγ1.le c) =
      (Real.pi : ℂ) * (cellA : ℂ) ^ 6 * c := by
  letI : IsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) :=
    @NormedSpace.toIsBoundedSMul ℝ (CircularConstrainedTangentSpace γ) _ _
      (innerDetectorTangent_space γ)
  letI : ContinuousSMul ℝ (CircularConstrainedTangentSpace γ) :=
    IsBoundedSMul.continuousSMul
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularConstrainedInnerPatchFourthMoment hγ hγle) 0
    (circularConstrainedUnstableEmbeddingCLM hγ hγle c) = (Real.pi : ℂ) * (cellA : ℂ) ^ 6 * c
  rw [(hasFDerivAt_circularConstrainedInnerPatchFourthMoment_zero hγ hγle).fderiv]
  change fderiv ℝ (circularAreaChartFourthMoment hγ hγle 0) 0
    ((circularConstrainedUnstableEmbeddingCLM hγ hγle c).val 0) = _
  rw [circularConstrainedUnstableEmbeddingCLM_val hγ hγle c, circularUnstableEmbeddingCLM_apply hγ hγle c,
    fderiv_circularAreaChartFourthMoment_normalMode hγ hγle]
  norm_num [circularContourRadii, vPlus, Pi.smul_apply, smul_eq_mul]

theorem exists_circularConstrainedInnerPatchFourthMoment_uniform_cone {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ m > 0, ∃ ε > 0, ε ≤ 1 ∧ ∃ r > 0,
      ∀ v : CircularConstrainedTangentSpace γ, v ∈ ball 0 r →
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      ‖v - α‖ ≤ ε * ‖α‖ →
      (m / 2) * ‖α‖ ≤ ‖circularConstrainedInnerPatchFourthMoment hγ hγ1.le v‖ := by
  let E := circularConstrainedUnstableEmbeddingCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let D := fderiv ℝ (circularConstrainedInnerPatchFourthMoment hγ hγ1.le) 0
  let p := Real.pi * cellA ^ 6
  let m := p / (‖E‖ + 1)
  have hp : 0 < p := by dsimp only [p]; have := cellA_pos; positivity
  have hm : 0 < m := div_pos hp (by positivity)
  have hmEq : m * (‖E‖ + 1) = p := div_mul_cancel₀ _ (by positivity)
  have hLower : ∀ α : CircularConstrainedTangentSpace γ, Q α = α → m * ‖α‖ ≤ ‖D α‖ := by
    intro α hα
    let c := circularConstrainedUnstableCoordinateCLM γ α
    have hemb : α = E c := by
      calc
        α = Q α := hα.symm
        _ = E c := by unfold Q circularConstrainedUnstableProjectionCLM; rfl
    have hαnorm : ‖α‖ ≤ (‖E‖ + 1) * ‖c‖ := by
      rw [hemb]
      exact (E.le_opNorm c).trans (mul_le_mul_of_nonneg_right (by linarith only [norm_nonneg E]) (norm_nonneg c))
    have hDnorm : ‖D α‖ = p * ‖c‖ := by
      rw [hemb, fderiv_circularConstrainedInnerPatchFourthMoment_unstableEmbedding hγ hγ1]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos cellA_pos, p]
    rw [hDnorm]
    calc
      _ ≤ m * ((‖E‖ + 1) * ‖c‖) := mul_le_mul_of_nonneg_left hαnorm hm.le
      _ = _ := by rw [← mul_assoc, hmEq]
  have hφD : HasFDerivAt (circularConstrainedInnerPatchFourthMoment hγ hγ1.le) D 0 :=
    (hasFDerivAt_circularConstrainedInnerPatchFourthMoment_zero hγ hγ1.le).differentiableAt.hasFDerivAt
  obtain ⟨ε, hε, hεOne, r, hr, hcone⟩ := exists_observable_departure_subspace_cone
    (φ := circularConstrainedInnerPatchFourthMoment hγ hγ1.le) (D := D) hφD hm
  refine ⟨m, hm, ε, hε, hεOne, r, hr, ?_⟩
  intro v hv
  dsimp only
  intro hclose
  have hbound := hcone v (Q v) hv
    (hLower (Q v) (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le v)) hclose
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  have hzero : circularConstrainedInnerPatchFourthMoment hγ hγle
      (0 : CircularConstrainedTangentSpace γ) = 0 :=
    circularConstrainedInnerPatchFourthMoment_zero hγ hγle
  change (m / 2) * ‖Q v‖ ≤ ‖circularConstrainedInnerPatchFourthMoment hγ hγle v -
    circularConstrainedInnerPatchFourthMoment hγ hγle 0‖ at hbound
  rw [hzero, sub_zero] at hbound
  change (m / 2) * ‖Q v‖ ≤ ‖circularConstrainedInnerPatchFourthMoment hγ hγle v‖
  exact hbound

end Euler2D

end
