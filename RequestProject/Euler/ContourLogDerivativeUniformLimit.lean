module

public import RequestProject.Euler.ContourLogDerivativeContinuity
public import RequestProject.Euler.ContourCauchyLocusCircle

/-! Uniform-norm continuity of the actual Hölder derivative on the
positive-chord locus. This uses actual Cauchy increments and actual phase
densities, and supplies the derivative limit for smooth approximations. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate BoundedContinuousFunction

namespace Euler2D

def positiveContourLogDerivativeBCF {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z : PositiveChordContour γ) : ContourCircle →ᵇ ℂ :=
  HolderFunctionSpace.toBCF γ (positiveContourLogDerivativeHolder hγ hγ1 Z)

theorem continuous_positiveContourLogDerivativeBCF {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Continuous (positiveContourLogDerivativeBCF hγ hγ1) := by
  let D : PositiveChordContour γ → (ContourCircle →ᵇ ℂ) := fun Z =>
    HolderFunctionSpace.toBCF γ (HolderFunctionSpace.conjugate (ContourC1Space.derivative γ Z.val))
  let C : PositiveChordContour γ → (ContourCircle →ᵇ ℂ) := fun Z =>
    contourCauchyIncrementBCF hγ (Z, positiveContourDerivativePhase Z)
  let J : (ContourCircle →ᵇ ℂ) →L[ℝ] (ContourCircle →ᵇ ℂ) :=
    Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ContourCircle
  have hD : Continuous D :=
    (HolderFunctionSpace.toBCF γ).continuous.comp
      ((HolderFunctionSpace.conjugateCLM γ).continuous.comp
        ((ContourC1Space.derivative γ).continuous.comp continuous_subtype_val))
  have hC : Continuous C :=
    (continuous_contourCauchyIncrementBCF hγ).comp
      (continuous_id.prodMk (continuous_positiveContourDerivativePhase γ))
  have hcomb : Continuous (fun Z => (1 / 2 : ℝ) • (D Z * J (C Z))) :=
    (hD.mul (J.continuous.comp hC)).const_smul (1 / 2 : ℝ)
  apply hcomb.congr
  intro Z
  apply BoundedContinuousFunction.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (1 / 2 : ℝ) •
    (conj (ContourC1Space.derivative γ Z.val (θ : ContourCircle)) *
      conj (contourC1CauchyIncrement Z.val (positiveContourDerivativePhase Z) θ)) =
    positiveContourLogDerivativeHolder hγ hγ1 Z (θ : ContourCircle)
  rw [positiveContourLogDerivativeHolder_apply, ← ContourC1Space.deriv_lift, Complex.real_smul]
  push_cast
  ring

theorem tendstoUniformly_positiveContourLogDerivative {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    {ι : Type*} {l : Filter ι} {u : ι → PositiveChordContour γ} {Z : PositiveChordContour γ}
    (hu : Tendsto u l (𝓝 Z)) :
    TendstoUniformly (fun i (θ : ℝ) =>
      positiveContourLogDerivativeHolder hγ hγ1 (u i) (θ : ContourCircle))
      (fun θ : ℝ => positiveContourLogDerivativeHolder hγ hγ1 Z (θ : ContourCircle)) l := by
  have h := ((continuous_positiveContourLogDerivativeBCF hγ hγ1).tendsto Z).comp hu
  exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h).comp
    (fun θ : ℝ => (θ : ContourCircle))

end Euler2D

end
