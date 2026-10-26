module

public import RequestProject.Euler.CircularCanonicalStageDeviation
public import RequestProject.Euler.ContinuousJointBootstrap

/-! The two joint bootstrap controls are continuous on the same
physical prefix trajectory. This does not require the bootstrap bounds. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 6500

noncomputable section

open Set
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

local instance controlFamilyRealSpace (γ : ℝ≥0) : NormedSpace ℝ (Fin 2 → LittleContourSpace γ) :=
  Pi.normedSpace
local instance controlFamilyComplexSpace (γ : ℝ≥0) : NormedSpace ℂ (Fin 2 → LittleContourSpace γ) :=
  Pi.normedSpace
local instance controlFamilyRealBounded (γ : ℝ≥0) : IsBoundedSMul ℝ (Fin 2 → LittleContourSpace γ) :=
  IsBoundedSMul.of_norm_smul_le (fun a Z => norm_smul_le a Z)
local instance controlFamilyComplexBounded (γ : ℝ≥0) : IsBoundedSMul ℂ (Fin 2 → LittleContourSpace γ) :=
  IsBoundedSMul.of_norm_smul_le (fun a Z => norm_smul_le a Z)
local instance controlFamilyRealContinuous (γ : ℝ≥0) : ContinuousSMul ℝ (Fin 2 → LittleContourSpace γ) :=
  IsBoundedSMul.continuousSMul
local instance controlFamilyComplexContinuous (γ : ℝ≥0) : ContinuousSMul ℂ (Fin 2 → LittleContourSpace γ) :=
  IsBoundedSMul.continuousSMul
local instance controlFamilyRealConstContinuous (γ : ℝ≥0) : ContinuousConstSMul ℝ (Fin 2 → LittleContourSpace γ) :=
  ContinuousSMul.continuousConstSMul

theorem continuousOn_canonicalPrefixAbsoluteCell {γ : ℝ≥0}
    (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ) {Dphys Dcap : ℝ}
    {X : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hX : ContinuousOn X (Icc (0 : ℝ) Dphys))
    (htime : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Dphys)) (j : Fin (k + 1)) :
    ContinuousOn (fun τ => canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ j) (Icc (0 : ℝ) Dcap) := by
  have hclock : Continuous (physicalTimeFromNormalized (ampScale A₀ b k) entrance) := by
    unfold physicalTimeFromNormalized
    fun_prop
  have hslice : Continuous (fun W : FiniteCircularIndex k → LittleContourSpace γ => fun i : Fin 2 => W (j, i)) :=
    continuous_pi (fun i => continuous_apply (j, i))
  have hcurve := hslice.comp_continuousOn (hX.comp hclock.continuousOn htime)
  have hgauge : Continuous (rigidRotationGauge (finiteAncestorAngularVelocity A₀ b j) 0) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_rigidRotationGauge _ _ t).continuousAt)
  unfold canonicalPrefixAbsoluteCell normalizedPhysicalCurve
  simpa only [Pi.smul_def', Pi.smul_def, Function.comp_def] using
    (hgauge.comp hclock).continuousOn.smul (hcurve.const_smul ((radScale R ρ j)⁻¹ : ℝ))

theorem continuousOn_canonicalPrefixStageDeviation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ) (entrance : ℝ)
    {Dphys Dcap : ℝ} {X : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hX : ContinuousOn X (Icc (0 : ℝ) Dphys))
    (htime : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Dphys)) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun τ => canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ j)
      (Icc (0 : ℝ) Dcap) := by
  have hcell := continuousOn_canonicalPrefixAbsoluteCell A₀ b R ρ k entrance hX htime ⟨j, Nat.lt_succ_of_le hj⟩
  have hreference : Continuous (fun τ : ℝ => littleCircularMaterialContours hγ hγ1
      (ampScale A₀ b j * entrance + b ^ (k - j) * τ)) :=
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous.comp (by fun_prop)
  simpa only [Pi.sub_def, canonicalPrefixStageDeviation, canonicalPrefixAbsoluteFamily, dif_pos hj] using
    hcell.sub hreference.continuousOn

theorem continuousOn_canonicalPrefix_joint_controls {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ h : ℝ) (k : ℕ) (entrance : ℝ)
    {Dphys Dcap : ℝ} {X : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
    (hX : ContinuousOn X (Icc (0 : ℝ) Dphys))
    (htime : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Dphys)) :
    (ContinuousOn (fun τ => weightedFamilyNorm h k
      (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ)) (Icc (0 : ℝ) Dcap)) ∧
    ContinuousOn (fun τ => ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ k‖)
      (Icc (0 : ℝ) Dcap) := by
  refine ⟨?_, (continuousOn_canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance hX htime k le_rfl).norm⟩
  apply ContinuousOn.norm
  apply continuousOn_pi.mpr
  intro j
  change ContinuousOn (fun τ : ℝ => ((h ^ (k - (j : ℕ)))⁻¹ : ℝ) •
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ (j : ℕ)) (Icc (0 : ℝ) Dcap)
  simpa only [Pi.smul_def] using
    (continuousOn_canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance hX htime j j.isLt.le).const_smul
      ((h ^ (k - (j : ℕ)))⁻¹ : ℝ)

end Euler2D

end
