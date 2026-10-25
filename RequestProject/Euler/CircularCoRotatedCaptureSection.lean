module

public import RequestProject.Euler.CircularCanonicalAncientGraphCells
public import RequestProject.Euler.CircularDeepestCaptureInitialState
public import RequestProject.Euler.CircularCanonicalContinuousControls
public import RequestProject.Euler.CircularCaptureBlockClock
public import RequestProject.Euler.ContinuousCaptureSection

/-! A first continuous section in the fixed graph coordinates, on the
same already existing material path and the same physical clock. Only
the full block endpoints use periodicity; intermediate projections are
not identified with the projections in the moving reference frame. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

theorem circularCoRotationCLM_capture_grid {γ : ℝ≥0} (n ℓ : ℕ)
    (Z : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ ((n : ℝ) * circularCaptureBlockTime ℓ) Z = Z := by
  have ht : (n : ℝ) * circularCaptureBlockTime ℓ =
      ((n * ℓ : ℕ) : ℝ) * (period + period) := by
    simp only [circularCaptureBlockTime, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [ht, circularCoRotationCLM_nat_double_period]

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedUnstableProjectionCLM
  contourC1GraphSubmodule holderGraphSubmodule

def HasFirstCircularCoRotatedCaptureSection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (y : ℝ → Fin 2 → LittleContourSpace γ) (D δ : ℝ) : Prop :=
  ∃ τ ∈ Ioc (0 : ℝ) D,
    ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δ ∧
    ∀ u ∈ Ico (0 : ℝ) τ,
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ

theorem exists_first_circularCoRotated_capture_section {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (n ℓ : ℕ) {δ : ℝ}
    (y : ℝ → Fin 2 → LittleContourSpace γ)
    (hD : 0 ≤ (n : ℝ) * circularCaptureBlockTime ℓ)
    (hy : ContinuousOn y (Icc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ)))
    (hstart : ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y 0 - littleCircularReference hγ hγ1))‖ < δ)
    (hend : δ ≤ ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1))‖) :
    ∃ τ ∈ Ioc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ),
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δ ∧
      ∀ u ∈ Ico (0 : ℝ) τ,
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ := by
  let z := fun τ : ℝ => circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))
  have hzc : ContinuousOn z (Icc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ)) :=
    (circularConstrainedUnstableProjectionCLM hγ hγ1.le).continuous.comp_continuousOn
      ((circularConstraintProjectionToTangentCLM hγ hγ1.le).continuous.comp_continuousOn
        ((continuousOn_circularCoRotatedCurve hγ1.le hy).sub continuousOn_const))
  apply exists_first_continuous_norm_section hD z hzc
  · dsimp only [z]
    rw [circularCoRotationCLM_zero]
    exact hstart
  · dsimp only [z]
    rw [circularCoRotationCLM_capture_grid]
    exact hend

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_first_actualDeepest_coRotated_section
    {s A₀ b R ρ a Hglob Dphys δ : ℝ} (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (N n ℓ : ℕ) (hℓ : 0 < ℓ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (X : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S Dphys X)
    (htime : ((n : ℝ) * circularCaptureBlockTime ℓ) / ampScale A₀ b N ≤ Dphys)
    (hstart : ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1))‖ < δ)
    (hend : δ ≤ ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
          ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1))‖) :
    ∃ τ ∈ Ioc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ),
      τ / ampScale A₀ b N ∈ Ioc (0 : ℝ) Dphys ∧
      ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
        (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ) -
            littleCircularReference hγ hγ1))‖ = δ ∧
      ∀ u ∈ Ico (0 : ℝ) τ,
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X u) -
              littleCircularReference hγ hγ1))‖ < δ := by
  have hAN : 0 < ampScale A₀ b N := by unfold ampScale; positivity
  have hD : 0 ≤ (n : ℝ) * circularCaptureBlockTime ℓ :=
    mul_nonneg (Nat.cast_nonneg n) (circularCaptureBlockTime_pos hℓ).le
  have htimes : MapsTo (physicalTimeFromNormalized (ampScale A₀ b N) 0)
      (Icc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ)) (Icc (0 : ℝ) Dphys) := by
    intro τ hτ
    change 0 ≤ 0 + τ / ampScale A₀ b N ∧ 0 + τ / ampScale A₀ b N ≤ Dphys
    rw [zero_add]
    exact ⟨div_nonneg hτ.1 hAN.le, (div_le_div_of_nonneg_right hτ.2 hAN.le).trans htime⟩
  have hyc : ContinuousOn (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X)
      (Icc (0 : ℝ) ((n : ℝ) * circularCaptureBlockTime ℓ)) := by
    have hyEq : canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X =
        (fun τ => canonicalPrefixAbsoluteCell A₀ b R ρ N 0 X τ (Fin.last N)) :=
      funext (fun τ => canonicalPrefixAlignedCurrentCell_zero_entrance A₀ b R ρ N X τ)
    rw [hyEq]
    exact continuousOn_canonicalPrefixAbsoluteCell A₀ b R ρ N 0 hX.continuous htimes (Fin.last N)
  obtain ⟨τ, hτ, hvalue, hfirst⟩ := exists_first_circularCoRotated_capture_section hγ hγ1 n ℓ
    (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X) hD hyc (by
      rw [P.actualCanonicalPrefix_initial_aligned_deepest hR hρ N S X hX]
      exact hstart) hend
  exact ⟨τ, hτ, ⟨div_pos hτ.1 hAN, (div_le_div_of_nonneg_right hτ.2 hAN.le).trans htime⟩,
    hvalue, hfirst⟩

end CircularMaterialTransferProfile
end Euler2D

end
