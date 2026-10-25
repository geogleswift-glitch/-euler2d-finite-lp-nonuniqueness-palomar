module

public import RequestProject.Euler.CircularConstrainedBackwardOrbit
public import RequestProject.Euler.BanachBackwardOrbitDeparture
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

local instance (priority := 2000) weightedBackwardLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) weightedBackwardLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) weightedBackwardFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) weightedBackwardTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) weightedBackwardTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) weightedBackwardTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) weightedBackwardEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) weightedBackwardTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem circularConstrainedReturn_hasFlatBackwardOrbits {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 1 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {w : ℝ} (hw : 2 < w) (hwa : w < lamMult ^ 2) :
    HasFlatBackwardOrbits
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w := by
  intro ε hε rmax hrmax
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hF : ContDiffAt ℝ 1 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hfd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.differentiableAt (by norm_num)
  have hcomm : L.comp P = P.comp L :=
    circularConstrainedReturnMap_derivative_projection_commute hγ hγ1 hR hX hfd hfix harea
  have hcommv (v : CircularConstrainedTangentSpace γ) : L (P v) = P (L v) :=
    congrArg (fun A : CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ => A v) hcomm
  have hcomm2 : (L ^ 2).comp P = P.comp (L ^ 2) := by
    apply ContinuousLinearMap.ext
    intro v
    change L (L (P v)) = P (L (L v))
    rw [hcommv, hcommv]
  have heigen1 (v : CircularConstrainedTangentSpace γ) : L (P v) = (-lamMult : ℝ) • P v := by
    change L (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) = _
    rw [circularConstrainedUnstableProjection_eq_embedding]
    exact circularConstrainedReturnMap_derivative_unstable hγ hγ1 hR hX hfd _
  have heigen2 (v : CircularConstrainedTangentSpace γ) : (L ^ 2) (P v) = lamMult ^ 2 • P v := by
    have h := continuousLinearMap_square_eigenvector L (P v) (-lamMult) (heigen1 v)
    simpa only [neg_sq] using h
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_circularConstrainedReturnMap_derivative_even_power_complement_le hγ hγ1 hR hX hfd hfix harea
  have hpower (k : ℕ) (v : CircularConstrainedTangentSpace γ) (hv : P v = 0) :
      ‖((L ^ 2) ^ k) v‖ ≤ C * (2 : ℝ) ^ k * ‖v‖ := by
    rw [← pow_mul]
    exact hbound k v hv
  exact exists_banachBackwardOrbit_of_kernel_bound (E := CircularConstrainedTangentSpace γ)
    (ρ := w) (a := lamMult ^ 2) (β := 2) (C := C) (banachDoubleReturn F)
    (contDiffAt_banachDoubleReturn hF0 hF) (banachDoubleReturn_zero hF0) (L ^ 2)
    (fderiv_banachDoubleReturn hF0 (hF.differentiableAt (by norm_num)))
    (by linarith : (1 : ℝ) < w) hwa (by norm_num : (0 : ℝ) ≤ 2)
    hw hC.le P
    (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le) hcomm2 heigen2 hpower hε hrmax

end Euler2D

end

