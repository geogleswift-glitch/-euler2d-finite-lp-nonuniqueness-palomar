module

public import RequestProject.Euler.CircularConstrainedReturnMap
public import RequestProject.Euler.CircularPeriodRotationCovariance
public import RequestProject.Euler.CircularPeriodAreaDerivative

/-! The genuine period derivative preserves the entire original
fourfold area tangent space. Consequently the derivative of the actual
constrained return map is its restriction, with no artificial projection. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) constrainedDerivLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedDerivLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) constrainedDerivFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) constrainedDerivTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedDerivTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedDerivTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

theorem circularPeriod_derivative_preserves_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (H : Fin 2 → LittleContourSpace γ)
    (hH : ∀ i, H i ∈ fourfoldLittleContourSubmodule γ) (i : Fin 2) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H i ∈
      fourfoldLittleContourSubmodule γ := by
  let D := fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
  let R := contourRotationFamilyLittleCLM (ι := Fin 2) γ (Real.pi / 2)
  have hRH : R H = H := by
    funext j
    have hj := hH j
    change contourRotationLittleCLM γ (Real.pi / 2) (H j) - H j = 0 at hj
    exact sub_eq_zero.mp hj
  have he : D (R H) = R (D H) :=
    congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) => A H)
      (circularPeriod_derivative_rotation_commute hγ hγ1 hρ hX hd (Real.pi / 2))
  have hRD : R (D H) = D H := he.symm.trans (congrArg D hRH)
  change contourRotationLittleCLM γ (Real.pi / 2) (D H i) - D H i = 0
  exact sub_eq_zero.mpr (congrFun hRD i)

theorem circularPeriod_derivative_preserves_constrainedTangent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (v : CircularConstrainedTangentSpace γ) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) v.val ∈
      circularConstrainedTangentSubmodule γ := by
  intro i
  refine ⟨circularPeriod_derivative_preserves_fourfold hγ hγ1 hρ hX hd v.val
    (fun j => (v.property j).1) i, ?_⟩
  change littleContourEllCLM γ (circularContourRadii i)
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) v.val i) = 0
  rw [circularPeriod_derivative_preserves_ell hγ hγ1 hρ hd hfix harea]
  exact (v.property i).2

theorem circularConstrainedReturnMap_derivative_val {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (v : CircularConstrainedTangentSpace γ) :
    (fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0 v).val =
      fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) v.val := by
  rw [(hasFDerivAt_circularConstrainedReturnMap_zero hγ hγ1 hd).fderiv]
  change circularConstraintProjectionCLM hγ hγ1.le
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) v.val) = _
  exact circularConstraintProjectionCLM_of_mem hγ hγ1.le _
    (circularPeriod_derivative_preserves_constrainedTangent hγ hγ1 hρ hX hd hfix harea v)

end Euler2D

end
