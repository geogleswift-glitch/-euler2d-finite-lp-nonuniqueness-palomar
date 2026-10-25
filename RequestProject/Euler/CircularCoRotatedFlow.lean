module

public import RequestProject.Euler.CircularReferencePhases
public import RequestProject.Euler.CircularReferenceQuadraticFlow
public import RequestProject.Euler.BanachFlowShiftCommutation
public import RequestProject.Euler.BanachUniformLinearBoundOfQuadratic

/-! The actual material flow in the fixed circular parameter frame.
This frame fixes the whole reference trajectory and has a genuine
uniform linear displacement bound throughout each compact time window. -/

@[expose] public section

set_option maxHeartbeats 400000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group quadraticReferenceLittle_group quadraticReferenceLittle_space
  quadraticReferenceFamily_tower

def circularCoRotationCLM (γ : ℝ≥0) (t : ℝ) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  contourParameterShiftFamilyCLM γ (fun i => -circularContourAngularVelocities i * t)

theorem circularCoRotationCLM_referenceTrajectory {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    circularCoRotationCLM γ t (littleCircularMaterialContours hγ hγ1 t) =
      littleCircularReference hγ hγ1 := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * t)
        (littleCircularMaterialContours hγ hγ1 t i)) θ =
    LittleContourSpace.lift γ (littleCircularReference hγ hγ1 i) θ
  rw [lift_contourParameterShiftLittleCLM, lift_littleCircularMaterialContours]
  change refCircle (circularContourRadii i)
      (θ + -circularContourAngularVelocities i * t + circularContourAngularVelocities i * t) =
    refCircle (circularContourRadii i) θ
  congr 1
  ring

theorem norm_circularCoRotationCLM {γ : ℝ≥0} (t : ℝ) (W : Fin 2 → LittleContourSpace γ) :
    ‖circularCoRotationCLM γ t W‖ = ‖W‖ := norm_contourParameterShiftFamilyCLM _ W

theorem norm_circularCoRotationCLM_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) (W : Fin 2 → LittleContourSpace γ) :
    ‖circularCoRotationCLM γ t W - littleCircularReference hγ hγ1‖ =
      ‖W - littleCircularMaterialContours hγ hγ1 t‖ := by
  rw [← circularCoRotationCLM_referenceTrajectory hγ hγ1 t, ← map_sub, norm_circularCoRotationCLM]

theorem circularBanachFlow_coRotated_commute {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R S H : ℝ}
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) S) H Y)
    {W : Fin 2 → LittleContourSpace γ}
    (hWX : W ∈ ball (littleCircularReference hγ hγ1) R)
    (hWY : W ∈ ball (littleCircularReference hγ hγ1) S)
    {t : ℝ} (ht : 0 ≤ t) (hH : t + period ≤ H)
    (hreturn : X W period ∈ ball (littleCircularReference hγ hγ1) S)
    (hshift : circularCoRotationCLM γ t (Y W t) ∈ ball (littleCircularReference hγ hγ1) R) :
    X (circularCoRotationCLM γ t (Y W t)) period =
      circularCoRotationCLM γ t (Y (X W period) t) := by
  exact hX.shift_symmetry_commute hY (isOpen_phaseAdmissibleLittleContourFamilies _ _)
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1)
    (by unfold period; positivity) (circularCoRotationCLM γ t)
    (fun z hz => circularBanachDomain_parameterShift hγ hγ1 _ hz)
    (fun z hz => circularBanachField_parameterShift hγ hγ1 _ hz)
    hWX hWY ht hH hreturn hshift

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference littleCircularMaterialContours
  contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circularCoRotatedFlow_uniform_linear_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) T X) :
    ∃ δ > 0, ∃ C > 0, ∀ W : Fin 2 → LittleContourSpace γ,
      ‖W - littleCircularReference hγ hγ1‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
        ‖circularCoRotationCLM γ t (X W t) - littleCircularReference hγ hγ1‖ ≤
          C * ‖W - littleCircularReference hγ hγ1‖ := by
  obtain ⟨A, hAc, hA0, hAd, δ, hδ, C, hC, hquad⟩ :=
    exists_circularReference_quadratic_variation hγ hγ1 hT hR hX
  obtain ⟨ε, hε, B, hB, hbound⟩ :=
    exists_uniform_linear_bound_of_quadratic_variation hAc.continuousOn hδ hC hquad
  refine ⟨ε, hε, B, hB, ?_⟩
  intro W hW t ht
  rw [norm_circularCoRotationCLM_sub_reference hγ hγ1]
  exact hbound W hW t ht

end Euler2D

end
