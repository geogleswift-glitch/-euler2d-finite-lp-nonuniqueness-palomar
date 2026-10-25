module

public import RequestProject.Euler.ContourLogDerivativeHolder
public import RequestProject.Euler.ContourDerivativePhaseContinuity

/-! The actual Hölder derivative is independent of the witness chosen
for a positive chord bound. This permits a canonical map on the open
positive-chord locus and subsequent limits of smooth contours. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate

namespace Euler2D

theorem contourLogDerivativeHolder_independent_lower {γ : ℝ≥0} (Z : ContourC1Space γ)
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hZc : ContourC1Space.HasChordArcLower Z c) (hZd : ContourC1Space.HasChordArcLower Z d) :
    contourLogDerivativeHolder Z hγ hγ1 hc hZc = contourLogDerivativeHolder Z hγ hγ1 hd hZd := by
  apply HolderFunctionSpace.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourLogDerivativeHolder_apply, contourLogDerivativeHolder_apply,
    contourDerivativePhase_independent_lower Z hc hd hZc hZd]

def positiveContourLogDerivativeHolder {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : PositiveChordContour γ) : ContourHolderSpace γ :=
  contourLogDerivativeHolder Z.val hγ hγ1 (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z)

theorem positiveContourLogDerivativeHolder_eq {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : PositiveChordContour γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z.val c) :
    positiveContourLogDerivativeHolder hγ hγ1 Z = contourLogDerivativeHolder Z.val hγ hγ1 hc hZ :=
  contourLogDerivativeHolder_independent_lower Z.val hγ hγ1 (positiveChordConstant_pos Z)
    hc (hasChordArcLower_positiveChordConstant Z) hZ

theorem positiveContourLogDerivativeHolder_apply {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (Z : PositiveChordContour γ) (θ : ℝ) :
    positiveContourLogDerivativeHolder hγ hγ1 Z (θ : ContourCircle) =
      (1 / 2 : ℂ) * conj (deriv (ContourC1Space.lift γ Z.val) θ) *
        conj (contourC1CauchyIncrement Z.val (positiveContourDerivativePhase Z) θ) := by
  exact contourLogDerivativeHolder_apply Z.val hγ hγ1 (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z) θ

end Euler2D

end
