module

public import RequestProject.Euler.CircularComplementPowerBound
public import RequestProject.Euler.CircularConstrainedSplitting

/-! The genuine full-space complement power bound transfers to the
actual constrained nonlinear return derivative, in its inherited Banach
norm and on the true kernel of its unstable projection. -/

@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem continuousLinearMap_intertwining_power_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E) (D : F →L[ℝ] F) (J : E →L[ℝ] F)
    (h : ∀ v, J (L v) = D (J v)) (k : ℕ) (v : E) :
    J ((L ^ k) v) = (D ^ k) (J v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = J (L ((L ^ k) v)) := by rw [pow_succ', ContinuousLinearMap.mul_apply]
      _ = D (J ((L ^ k) v)) := h _
      _ = D ((D ^ k) (J v)) := congrArg D ih
      _ = _ := by rw [pow_succ', ContinuousLinearMap.mul_apply]

local instance (priority := 2000) constrainedPowerLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) constrainedPowerLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) constrainedPowerFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) constrainedPowerTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedPowerTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) constrainedPowerTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) constrainedPowerEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid

theorem circularConstrainedTangentSpace_component_constraints {γ : ℝ≥0}
    (v : CircularConstrainedTangentSpace γ) (i : Fin 2) :
    v.val i ∈ fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) :=
  v.property i

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM

section ActualReturn

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
variable {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
variable (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
  (ball (littleCircularReference hγ hγ1) ρ) period X)
variable (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
variable (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
variable (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) ρ, ∀ i,
  littleContourArea γ (X W period i) = littleContourArea γ (W i))

include hρ hX hd hfix harea

theorem circularConstrainedReturnMap_derivative_pow_val (k : ℕ) (v : CircularConstrainedTangentSpace γ) :
    (((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ k) v).val =
      ((fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) ^ k) v.val := by
  exact continuousLinearMap_intertwining_power_apply
    (fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0)
    (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (circularConstrainedTangentSubmodule γ).subtypeL
    (fun w => circularConstrainedReturnMap_derivative_val hγ hγ1 hρ hX hd hfix harea w) k v

theorem exists_norm_circularConstrainedReturnMap_derivative_even_power_complement_le :
    ∃ C > 0, ∀ (k : ℕ) (v : CircularConstrainedTangentSpace γ),
      v ∈ (circularConstrainedUnstableProjectionCLM hγ hγ1.le).ker →
        ‖((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ (2 * k)) v‖ ≤
          C * (2 : ℝ) ^ k * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_circularPeriod_derivative_even_power_complement_le hγ hγ1 hρ hX hd
  refine ⟨C, hC, ?_⟩
  intro k v hv
  change circularConstrainedUnstableProjectionCLM hγ hγ1.le v = 0 at hv
  have hraw : circularUnstableProjectionCLM hγ hγ1.le v.val = 0 :=
    (circularConstrainedUnstableProjectionCLM_val hγ hγ1.le v).symm.trans
      (congrArg (fun w : CircularConstrainedTangentSpace γ => w.val) hv)
  have h := hbound k v.val
    (fun i => (circularConstrainedTangentSpace_component_constraints v i).1)
    (fun i => (circularConstrainedTangentSpace_component_constraints v i).2) hraw
  change ‖(((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ (2 * k)) v).val‖ ≤
    C * (2 : ℝ) ^ k * ‖v.val‖
  rw [circularConstrainedReturnMap_derivative_pow_val hγ hγ1 hρ hX hd hfix harea]
  exact h

end ActualReturn

end Euler2D

end
