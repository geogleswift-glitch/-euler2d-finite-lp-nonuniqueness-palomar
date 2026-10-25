module

public import RequestProject.Euler.CircularUnstableProjection
public import RequestProject.Euler.CircularFourierRotationProjection

/-! The genuine growing projection commutes with the original return
derivative, so its closed complementary kernel is invariant. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) unstableComplementLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) unstableComplementLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem ellPlus_circularNormalGenerator (η : CircularFourierVector) :
    ellPlus (circularNormalGenerator 2 η) = lamStar * ellPlus η :=
  ellPlus_left_eigen η

theorem ellPlus_circularNormalLinearFlow_hasDerivAt (η : CircularFourierVector) (t : ℝ) :
    HasDerivAt (fun s => ellPlus (circularNormalLinearFlow 2 η s))
      (lamStar * ellPlus (circularNormalLinearFlow 2 η t)) t := by
  have hd := circularEllPlusCLM.hasFDerivAt.comp_hasDerivAt t
    (circularNormalLinearFlow_hasDerivAt 2 η t)
  simpa only [Function.comp_def, circularEllPlusCLM_apply, ellPlus_circularNormalGenerator] using hd

theorem ellPlus_circularNormalLinearFlow (η : CircularFourierVector)
    {t : ℝ} (ht : 0 ≤ t) :
    ellPlus (circularNormalLinearFlow 2 η t) = exp ((t : ℂ) * lamStar) * ellPlus η := by
  let B : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) lamStar
  let α : ℝ → ℂ := fun s => ellPlus (circularNormalLinearFlow 2 η s)
  let β : ℝ → ℂ := fun s => exp ((s : ℂ) * lamStar) * ellPlus η
  have hα (s : ℝ) : HasDerivAt α (B (α s)) s :=
    ellPlus_circularNormalLinearFlow_hasDerivAt η s
  have hβ (s : ℝ) : HasDerivAt β (B (β s)) s := by
    have hd := (hasDerivAt_circularGrowingScalar s).mul_const (ellPlus η)
    convert hd using 1 <;> dsimp only [β, B, ContinuousLinearMap.mul_apply'] <;> ring
  have hαc : Continuous α := continuous_iff_continuousAt.mpr (fun s => (hα s).continuousAt)
  have hβc : Continuous β := continuous_iff_continuousAt.mpr (fun s => (hβ s).continuousAt)
  have he : EqOn α β (Icc (0 : ℝ) t) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ z => B z) (s := fun _ => (univ : Set ℂ))
      (fun _ _ => B.lipschitz.lipschitzOnWith)
      hαc.continuousOn (fun s _ => (hα s).hasDerivWithinAt) (fun _ _ => mem_univ _)
      hβc.continuousOn (fun s _ => (hβ s).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (by simp only [α, β, circularNormalLinearFlow_zero, ofReal_zero, zero_mul, exp_zero, one_mul])
  exact he ⟨ht, le_rfl⟩

theorem ellPlus_circularNormalLinearFlow_period (η : CircularFourierVector) :
    ellPlus (circularNormalLinearFlow 2 η period) = (-lamMult : ℝ) • ellPlus η := by
  rw [ellPlus_circularNormalLinearFlow η (show 0 ≤ period by unfold period; positivity),
    period_multipliers_m4.1]
  simp only [Complex.real_smul, Complex.ofReal_neg]

theorem circularUnstableCoordinate_fourthProjection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableCoordinateCLM γ (circularFourthModeProjectionCLM hγ hγ1 H) =
      circularUnstableCoordinateCLM γ H := by
  change circularEllPlusCLM (circularFourthNormalCoefficientCLM γ
    (circularFourthModeProjectionCLM hγ hγ1 H)) = _
  rw [circularFourthModeProjectionCLM_eq_normalMode, circularFourthNormalCoefficientCLM_normalMode]
  rfl

theorem circularUnstableProjection_fourthProjection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableProjectionCLM hγ hγ1 (circularFourthModeProjectionCLM hγ hγ1 H) =
      circularUnstableProjectionCLM hγ hγ1 H := by
  rw [circularUnstableProjectionCLM_apply, circularUnstableProjectionCLM_apply,
    circularUnstableCoordinate_fourthProjection]

theorem circularUnstableCoordinate_normalMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : CircularFourierVector) :
    circularUnstableCoordinateCLM γ (circularNormalModeLittle hγ hγ1 2 η τ) = ellPlus η := by
  change circularEllPlusCLM (circularFourthNormalCoefficientCLM γ
    (circularNormalModeLittle hγ hγ1 2 η τ)) = _
  rw [circularFourthNormalCoefficientCLM_normalMode, circularEllPlusCLM_apply]

set_option maxHeartbeats 800000 in
theorem circularPeriod_derivative_unstableCoordinate {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableCoordinateCLM γ
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) =
      (-lamMult : ℝ) • circularUnstableCoordinateCLM γ H := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let P := circularFourthModeProjectionCLM hγ hγle
  have hc : D (P H) = P (D H) :=
    congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ]
      (Fin 2 → LittleContourSpace γ) => A H)
      (circularPeriod_derivative_fourthProjection_commute hγ hγ1 hρ hX hd)
  change circularUnstableCoordinateCLM γ (D H) = _
  rw [← circularUnstableCoordinate_fourthProjection hγ hγle (D H), ← hc]
  dsimp only [P, D]
  rw [circularFourthModeProjectionCLM_eq_normalMode hγ hγle H]
  have hblock : fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγle 2
        (circularFourthNormalCoefficientCLM γ H) (circularFourthTangentCoefficientCLM γ H)) =
    circularNormalModeLittle hγ hγle 2
      (circularNormalLinearFlow 2 (circularFourthNormalCoefficientCLM γ H) period)
      (circularAmplitudeLinearFlow 2
        (circularFourthNormalCoefficientCLM γ H, circularFourthTangentCoefficientCLM γ H) period).2 :=
    circularPeriod_derivative_Fourier_block hγ hγ1 hρ hX 2
      (circularFourthNormalCoefficientCLM γ H) (circularFourthTangentCoefficientCLM γ H)
  rw [hblock, circularUnstableCoordinate_normalMode hγ hγle,
    ellPlus_circularNormalLinearFlow_period]
  change (-lamMult : ℝ) • ellPlus (circularFourthNormalCoefficientCLM γ H) =
    (-lamMult : ℝ) • circularEllPlusCLM (circularFourthNormalCoefficientCLM γ H)
  rw [circularEllPlusCLM_apply]

theorem circularPeriod_derivative_unstableProjection_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) :
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)).comp
        (circularUnstableProjectionCLM hγ hγ1.le) =
      (circularUnstableProjectionCLM hγ hγ1.le).comp
        (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) := by
  apply ContinuousLinearMap.ext
  intro H
  change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularUnstableProjectionCLM hγ hγ1.le H) =
    circularUnstableEmbeddingCLM hγ hγ1.le (circularUnstableCoordinateCLM γ
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H))
  rw [circularPeriod_derivative_unstableProjection_apply hγ hγ1 hρ hX,
    circularPeriod_derivative_unstableCoordinate hγ hγ1 hρ hX hd]
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change (-lamMult : ℝ) • circularUnstableProjectionCLM hγ hγle H =
    circularUnstableEmbeddingCLM hγ hγle ((-lamMult : ℝ) • circularUnstableCoordinateCLM γ H)
  rw [circularUnstableProjectionCLM_apply hγ hγle H]
  exact ((circularUnstableEmbeddingCLM hγ hγle).toLinearMap.map_smul'
    (-lamMult : ℝ) (circularUnstableCoordinateCLM γ H)).symm

theorem circularPeriod_derivative_unstableComplement_invariant {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    {H : Fin 2 → LittleContourSpace γ}
    (hH : H ∈ (circularUnstableProjectionCLM hγ hγ1.le).ker) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H ∈
      (circularUnstableProjectionCLM hγ hγ1.le).ker := by
  change circularUnstableProjectionCLM hγ hγ1.le
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) = 0
  have he := congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ]
    (Fin 2 → LittleContourSpace γ) => A H)
    (circularPeriod_derivative_unstableProjection_commute hγ hγ1 hρ hX hd)
  change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularUnstableProjectionCLM hγ hγ1.le H) = circularUnstableProjectionCLM hγ hγ1.le
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H) at he
  rw [← he]
  change circularUnstableProjectionCLM hγ hγ1.le H = 0 at hH
  rw [hH, map_zero]

end Euler2D

end
