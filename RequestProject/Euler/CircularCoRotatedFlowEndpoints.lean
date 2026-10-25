module

public import RequestProject.Euler.CircularCoRotatedCurveContinuity
public import RequestProject.Euler.CircularBackwardGraphTimeInvariance

/-! Exact endpoints of the actual co-parameter flow. The circular
material shift is the identity after one period on every original
little contour, and genuine short/long flows agree by uniqueness. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space localGraphTangent_continuousAdd

theorem circularCoRotationCLM_zero (γ : ℝ≥0) (W : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ 0 W = W := by
  unfold circularCoRotationCLM
  have hz : (fun i : Fin 2 => -circularContourAngularVelocities i * (0 : ℝ)) = 0 := by
    funext i
    simp only [mul_zero, Pi.zero_apply]
  rw [hz, contourParameterShiftFamilyCLM_zero]

theorem circularCoRotationCLM_period (γ : ℝ≥0) (W : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ period W = W := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * period) (W i)) θ =
    LittleContourSpace.lift γ (W i) θ
  rw [lift_contourParameterShiftLittleCLM]
  fin_cases i
  · change LittleContourSpace.lift γ (W 0) (θ + -(1 / 2 : ℝ) * period) =
      LittleContourSpace.lift γ (W 0) θ
    rw [show θ + -(1 / 2 : ℝ) * period = θ - 2 * Real.pi by unfold period; ring]
    have hp := LittleContourSpace.periodic_lift (W 0) (θ - 2 * Real.pi)
    rw [sub_add_cancel] at hp
    exact hp.symm
  · change LittleContourSpace.lift γ (W 1) (θ + -(0 : ℝ) * period) =
      LittleContourSpace.lift γ (W 1) θ
    simp only [neg_zero, zero_mul, add_zero]

theorem circularCoRotationCLM_add (γ : ℝ≥0) (t u : ℝ) (W : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ t (circularCoRotationCLM γ u W) = circularCoRotationCLM γ (t + u) W := by
  unfold circularCoRotationCLM
  rw [contourParameterShiftFamilyCLM_add]
  have hp : (fun i : Fin 2 => -circularContourAngularVelocities i * t) +
      (fun i => -circularContourAngularVelocities i * u) =
      (fun i => -circularContourAngularVelocities i * (t + u)) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [hp]

theorem circularConstrainedChart_projection_left_inverse {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (v : CircularConstrainedTangentSpace γ) :
    circularConstraintProjectionToTangentCLM hγ hγ1.le
      (circularConstrainedChart hγ hγ1 v - littleCircularReference hγ hγ1) = v := by
  apply Subtype.ext
  rw [circularConstraintProjectionToTangentCLM_val,
    circularConstraintProjection_sub_reference hγ hγ1 _ (circularConstrainedChart_fourfold hγ hγ1 v)]
  exact circularAreaChartInverseFamily_chart hγ hγ1 v

theorem circularCoRotatedConstrainedMap_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {V : Set (Fin 2 → LittleContourSpace γ)} {T : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) V T X)
    (v : CircularConstrainedTangentSpace γ) (hv : circularConstrainedChart hγ hγ1 v ∈ V) :
    circularCoRotatedConstrainedMap hγ hγ1 X 0 v = v := by
  unfold circularCoRotatedConstrainedMap circularConstrainedReturnMap
  dsimp only
  rw [hX.initial _ hv, circularCoRotationCLM_zero]
  exact circularConstrainedChart_projection_left_inverse hγ hγ1 v

attribute [local irreducible] circularBanachField circularBanachDomain littleCircularReference
  circularConstrainedTangentSubmodule circularConstrainedChart circularConstraintProjectionToTangentCLM
  contourC1GraphSubmodule holderGraphSubmodule

theorem circularBanachFlows_agree_at_period {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {V U : Set (Fin 2 → LittleContourSpace γ)} {H : ℝ}
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) V period X)
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) U H Y)
    (hH : period ≤ H) {W : Fin 2 → LittleContourSpace γ} (hWX : W ∈ V) (hWY : W ∈ U) :
    Y W period = X W period := by
  have hdom : IsOpen (circularBanachDomain hγ hγ1) := by
    unfold circularBanachDomain
    exact isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) := by
    unfold circularBanachField circularBanachDomain
    exact contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
  have he : EqOn (X W) (Y W) (Icc (0 : ℝ) period) := by
    apply eqOn_of_banachODE_open hdom hf
      (hX.continuous W hWX) ((hY.continuous W hWY).mono (Icc_subset_Icc_right hH))
      (hX.mem W hWX) (fun t ht => hY.mem W hWY t ⟨ht.1, ht.2.trans hH⟩)
      (fun t ht => hX.hasDerivAt W hWX t ⟨ht.1, ht.2.le⟩)
      (fun t ht => hY.hasDerivAt W hWY t ⟨ht.1, ht.2.le.trans hH⟩)
    rw [hX.initial W hWX, hY.initial W hWY]
  exact (he ⟨by unfold period; positivity, le_rfl⟩).symm

theorem circularCoRotatedConstrainedMap_period {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {V U : Set (Fin 2 → LittleContourSpace γ)} {H : ℝ}
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) V period X)
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) U H Y)
    (hH : period ≤ H) (v : CircularConstrainedTangentSpace γ)
    (hvX : circularConstrainedChart hγ hγ1 v ∈ V) (hvY : circularConstrainedChart hγ hγ1 v ∈ U) :
    circularCoRotatedConstrainedMap hγ hγ1 Y period v =
      circularConstrainedReturnMap hγ hγ1 (fun W => X W period) v := by
  unfold circularCoRotatedConstrainedMap circularConstrainedReturnMap
  dsimp only
  rw [circularCoRotationCLM_period, circularBanachFlows_agree_at_period hγ hγ1 hX hY hH hvX hvY]

end Euler2D

end
