module

public import RequestProject.Euler.CircularDoublePeriodOperator

/-! The omitted low contour modes form the true sum of the zero
and first angular blocks. The genuine derivative preserves their kernel,
and the actual Fourier smoothing operator has no low part. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) lowCalcLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) lowCalcLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) lowCalcFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

theorem circularLowFourierProjectionCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) (i : Fin 2) :
    circularLowFourierProjectionCLM hγ hγ1 H i =
      littleContourFourierMode hγ hγ1 0 (littleContourFourierCoefficient γ 0 (H i)) +
        littleContourFourierMode hγ hγ1 1 (littleContourFourierCoefficient γ 1 (H i)) +
          littleContourFourierMode hγ hγ1 2 (littleContourFourierCoefficient γ 2 (H i)) := by
  simp only [circularLowFourierProjectionCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.add_apply,
    littleContourFourierTermCLM_apply, one_mul]

theorem circularLowFourierProjectionCLM_eq_angular {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularLowFourierProjectionCLM hγ hγ1 H =
      (1 / 2 : ℝ) • circularAngularModeProjectionCLM hγ hγ1 0 H +
        circularAngularModeProjectionCLM hγ hγ1 1 H := by
  funext i
  rw [circularLowFourierProjectionCLM_apply]
  change _ = (1 / 2 : ℝ) • contourAngularModeProjectionCLM hγ hγ1 0 (H i) +
    contourAngularModeProjectionCLM hγ hγ1 1 (H i)
  rw [contourAngularModeProjectionCLM_apply, contourAngularModeProjectionCLM_apply]
  norm_num only [Int.add_zero, Int.sub_zero, show (1 : ℤ) + 1 = 2 by norm_num,
    show (1 : ℤ) - 1 = 0 by norm_num]
  module

theorem circularLowFourierProjectionCLM_embedding_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (p : CircularFourierAmplitudes) :
    circularLowFourierProjectionCLM hγ hγ1 (circularModeAmplitudeEmbeddingCLM hγ hγ1 N p) = 0 := by
  funext i
  have hz (k : ℤ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2) :
      littleContourFourierCoefficient γ k (circularModeAmplitudeEmbeddingCLM hγ hγ1 N p i) = 0 := by
    rw [circularModeAmplitudeEmbeddingCLM_apply, littleContourFourierCoefficient_circularNormalMode]
    rw [if_neg (by omega : ((N + 3 : ℕ) : ℤ) ≠ k),
      if_neg (by omega : -((N + 1 : ℕ) : ℤ) ≠ k), zero_add]
  rw [circularLowFourierProjectionCLM_apply, hz 0 (by norm_num) (by norm_num),
    hz 1 (by norm_num) (by norm_num), hz 2 (by norm_num) (by norm_num)]
  have hmode (k : ℤ) : littleContourFourierMode hγ hγ1 k 0 = 0 := by
    rw [← littleContourFourierModeCLM_apply]
    exact (littleContourFourierModeCLM hγ hγ1 k).map_zero
  rw [hmode, hmode, hmode, zero_add, zero_add]
  rfl

theorem circularLowFourierProjectionCLM_multiplier_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖))
    (H : Fin 2 → LittleContourSpace γ) :
    circularLowFourierProjectionCLM hγ hγ1 (circularFourierBlockMultiplierCLM hγ hγ1 A H) = 0 := by
  have hs := summable_circularFourierBlockTermCLM hγ hγ1 hA
  let ev : ((Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ)) →L[ℝ]
      (Fin 2 → LittleContourSpace γ) := ContinuousLinearMap.apply ℝ _ H
  have hlow := (circularLowFourierProjectionCLM hγ hγ1).hasSum (ev.hasSum hs.hasSum)
  have hz (N : ℕ) : circularLowFourierProjectionCLM hγ hγ1
      (circularFourierBlockTermCLM hγ hγ1 N (A N) H) = 0 :=
    circularLowFourierProjectionCLM_embedding_zero hγ hγ1 N _
  change circularLowFourierProjectionCLM hγ hγ1
    (ev (∑' N, circularFourierBlockTermCLM hγ hγ1 N (A N))) = _
  rw [← hlow.tsum_eq]
  change (∑' N, circularLowFourierProjectionCLM hγ hγ1
    (circularFourierBlockTermCLM hγ hγ1 N (A N) H)) = 0
  simp only [hz, tsum_zero]

theorem circularPeriod_derivative_lowProjection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)).comp
        (circularLowFourierProjectionCLM hγ hγ1.le) =
      (circularLowFourierProjectionCLM hγ hγ1.le).comp
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) := by
  apply ContinuousLinearMap.ext
  intro H
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let Q0 := circularAngularModeProjectionCLM hγ hγ1.le 0
  let Q1 := circularAngularModeProjectionCLM hγ hγ1.le 1
  have he0 : D (Q0 H) = Q0 (D H) := congrArg (fun A => A H)
    (circularPeriod_derivative_angularProjection_commute hγ hγ1 hρ hX hd 0)
  have he1 : D (Q1 H) = Q1 (D H) := congrArg (fun A => A H)
    (circularPeriod_derivative_angularProjection_commute hγ hγ1 hρ hX hd 1)
  change D (circularLowFourierProjectionCLM hγ hγ1.le H) =
    circularLowFourierProjectionCLM hγ hγ1.le (D H)
  rw [circularLowFourierProjectionCLM_eq_angular, map_add]
  have hsmul : D ((1 / 2 : ℝ) • Q0 H) = (1 / 2 : ℝ) • D (Q0 H) :=
    D.toLinearMap.map_smul' (1 / 2 : ℝ) (Q0 H)
  change D ((1 / 2 : ℝ) • Q0 H) + D (Q1 H) = _
  rw [hsmul, he0, he1]
  exact (circularLowFourierProjectionCLM_eq_angular hγ hγ1.le (D H)).symm

end Euler2D

end
