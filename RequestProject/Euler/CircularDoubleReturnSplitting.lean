module

public import RequestProject.Euler.CircularWeightedBackwardOrbit
public import RequestProject.Euler.CircularSharpOrbitWeight
public import RequestProject.Euler.CircularHyperbolicGap
public import RequestProject.Euler.BanachDoubleReturn
public import RequestProject.Euler.BanachNonlinearKernelOrbit

/-! Genuine nonlinear ancient discrete orbits of the original
fourfold fixed-area return map. The full original Banach power bound,
actual unstable projection, and true derivative are used directly. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) doubleSplitLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) doubleSplitLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) doubleSplitFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) doubleSplitTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) doubleSplitTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) doubleSplitTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) doubleSplitEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) doubleSplitTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

section ActualReturn

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
variable {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
variable (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
  (ball (littleCircularReference hγ hγ1) R) period X)
variable (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
variable (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
variable (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
  littleContourArea γ (X W period i) = littleContourArea γ (W i))

include hR hX hd hfix harea

theorem circularConstrainedDoubleDerivative_projection_commute :
    ((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ 2).comp
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) =
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le).comp
        ((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ 2) := by
  let L := fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hcomm : L.comp P = P.comp L :=
    circularConstrainedReturnMap_derivative_projection_commute hγ hγ1 hR hX hd hfix harea
  have hv (v : CircularConstrainedTangentSpace γ) : L (P v) = P (L v) :=
    congrArg (fun A : CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ => A v) hcomm
  apply ContinuousLinearMap.ext
  intro v
  change L (L (P v)) = P (L (L v))
  rw [hv, hv]

theorem circularConstrainedDoubleDerivative_projection_eigen (v : CircularConstrainedTangentSpace γ) :
    ((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ 2)
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) =
      lamMult ^ 2 • circularConstrainedUnstableProjectionCLM hγ hγ1.le v := by
  let L := fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have he : L (P v) = (-lamMult : ℝ) • P v := by
    have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
    change L (circularConstrainedUnstableProjectionCLM hγ hγle v) =
      (-lamMult : ℝ) • circularConstrainedUnstableProjectionCLM hγ hγle v
    rw [circularConstrainedUnstableProjection_eq_embedding hγ hγle v]
    exact circularConstrainedReturnMap_derivative_unstable hγ hγ1 hR hX hd _
  simpa only [neg_sq] using continuousLinearMap_square_eigenvector L (P v) (-lamMult) he

theorem exists_norm_circularConstrainedDoubleDerivative_complement_power_le :
    ∃ C > 0, ∀ (k : ℕ) (v : CircularConstrainedTangentSpace γ),
      circularConstrainedUnstableProjectionCLM hγ hγ1.le v = 0 →
      ‖(((fderiv ℝ (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)) 0) ^ 2) ^ k) v‖ ≤
        C * (2 : ℝ) ^ k * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_circularConstrainedReturnMap_derivative_even_power_complement_le hγ hγ1 hR hX hd hfix harea
  refine ⟨C, hC, ?_⟩
  intro k v hv
  rw [← pow_mul]
  exact hbound k v hv

end ActualReturn

theorem circularConstrainedReturn_hasSharpBackwardOrbits {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i)) :
    HasFlatBackwardOrbits
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight := by
  exact circularConstrainedReturn_hasFlatBackwardOrbits hγ hγ1 hR hX hd hfix harea
    circularAncientBackwardWeight_bounds.1 circularAncientBackwardWeight_bounds.2

end Euler2D

end
