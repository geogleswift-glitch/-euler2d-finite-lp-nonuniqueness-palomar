module

public import RequestProject.Euler.ContourHolderInverseAnalytic
public import RequestProject.Euler.ContourDerivativePhaseContinuity

/-! Actual higher input regularity of the contour density `conj Z'/Z'`.
The input derivative is the genuine derivative CLM of the actual contour
space.  The total local presentation agrees exactly with the original
derivative phase wherever a true positive chord bound holds. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ComplexConjugate ContDiff

namespace Euler2D

local instance (priority := 2000) phaseAnalytic_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) phaseAnalytic_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

/-- A total local presentation of the true contour derivative phase. -/
def analyticContourDerivativePhase (γ : ℝ≥0) (Z : ContourC1Space γ) : ContourHolderSpace γ :=
  HolderFunctionSpace.phase γ (ContourC1Space.derivative γ Z)

theorem analyticContourDerivativePhase_eq {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c) :
    analyticContourDerivativePhase γ Z = contourDerivativePhase Z hc hZ :=
  (HolderFunctionSpace.phase_eq_phaseOfNormLower (ContourC1Space.derivative γ Z)
    hc (contourC1_derivative_norm_lower Z hZ)).trans
      (contourDerivativePhase_eq_phaseOfNormLower Z hc hZ).symm

theorem analyticContourDerivativePhase_apply {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c) (θ : ℝ) :
    analyticContourDerivativePhase γ Z (θ : ContourCircle) =
      conj (deriv (ContourC1Space.lift γ Z) θ) / deriv (ContourC1Space.lift γ Z) θ := by
  rw [analyticContourDerivativePhase_eq Z hc hZ]
  exact contourDerivativePhase_apply Z hc hZ θ

/-- Genuine Banach-input real analyticity of the actual density. -/
theorem analyticAt_contourDerivativePhase {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℝ (analyticContourDerivativePhase γ) Z := by
  have hp := HolderFunctionSpace.analyticAt_phase (ContourC1Space.derivative γ Z)
    hc (contourC1_derivative_norm_lower Z hZ)
  exact (hp.comp ((ContourC1Space.derivative γ).analyticAt Z)).congr
    (Eventually.of_forall (fun _ => rfl))

theorem analyticOnNhd_contourDerivativePhase (γ : ℝ≥0) :
    AnalyticOnNhd ℝ (analyticContourDerivativePhase γ)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  rintro Z ⟨c, hc, hZ⟩
  exact analyticAt_contourDerivativePhase Z hc hZ

theorem contDiffAt_contourDerivativePhase {γ : ℝ≥0} (Z : ContourC1Space γ)
    {c : ℝ} (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (analyticContourDerivativePhase γ) Z :=
  (analyticAt_contourDerivativePhase Z hc hZ).contDiffAt

theorem contDiffOn_contourDerivativePhase (γ : ℝ≥0) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (analyticContourDerivativePhase γ)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  rintro Z ⟨c, hc, hZ⟩
  exact (contDiffAt_contourDerivativePhase Z hc hZ n).contDiffWithinAt

theorem analyticContourDerivativePhase_eq_positive {γ : ℝ≥0} (Z : PositiveChordContour γ) :
    analyticContourDerivativePhase γ Z.val = positiveContourDerivativePhase Z :=
  analyticContourDerivativePhase_eq Z.val (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z)

end Euler2D

end
