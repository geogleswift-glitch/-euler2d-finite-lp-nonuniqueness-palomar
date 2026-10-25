module

public import RequestProject.Euler.ContourComplexC1Space
public import RequestProject.Euler.ContourComplexHolderInverse
public import RequestProject.Euler.ContourCauchyShapeKernel
public import RequestProject.Euler.ContourDerivativePhase
public import RequestProject.Euler.ContourAdmissibility

/-! Actual holomorphic normalized contour quotients.  Every map is built
from the actual periodic lift and actual derivative.  The existing real
graph and its norm are retained; complex structures are enabled locally. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal BoundedContinuousFunction

attribute [local instance] Euler2D.HolderFunctionSpace.complexScalarNormedSpace
attribute [local instance] Euler2D.HolderFunctionSpace.complexScalarTower
attribute [local instance] Euler2D.ContourC1Space.complexScalarNormedSpace
attribute [local instance] Euler2D.ContourC1Space.complexScalarTower

namespace Euler2D

variable {γ : ℝ≥0}

def contourComplexHolderShiftCLM (γ : ℝ≥0) (τ : ℝ) :
    ContourHolderSpace γ →L[ℂ] ContourHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := fun f => contourHolderShift f τ
      map_add' := by
        intro f g
        apply HolderFunctionSpace.ext
        intro x
        rfl
      map_smul' := by
        intro a f
        apply HolderFunctionSpace.ext
        intro x
        rfl }
    1 (fun f => by simpa only [one_mul] using norm_contourHolderShift_le f τ)

def contourComplexNormalizedChordCLM (hγ : 0 < (γ : ℝ)) (τ : ℝ) :
    ContourC1Space γ →L[ℂ] ContourHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := fun Z => contourNormalizedChord hγ Z τ
      map_add' := by
        intro Z W
        apply HolderFunctionSpace.ext
        intro x
        by_cases hτ : τ = 0
        · simp only [contourNormalizedChord_apply, contourNormalizedChordFunction, if_pos hτ,
            map_add, HolderFunctionSpace.add_apply]
          abel
        · simp only [contourNormalizedChord_apply, contourNormalizedChordFunction, if_neg hτ,
            map_add, BoundedContinuousFunction.add_apply, HolderFunctionSpace.add_apply]
          rw [← smul_add]
          congr 1
          abel
      map_smul' := by
        intro a Z
        apply HolderFunctionSpace.ext
        intro x
        change contourNormalizedChordFunction (ContourC1Space.complexScale a Z) τ x =
          a * contourNormalizedChordFunction Z τ x
        by_cases hτ : τ = 0
        · simp only [contourNormalizedChordFunction, if_pos hτ]
          change -(a * ContourC1Space.derivative γ Z x) =
            a * (-ContourC1Space.derivative γ Z x)
          ring
        · simp only [contourNormalizedChordFunction, if_neg hτ]
          change τ⁻¹ • (a * ContourC1Space.toBCF γ Z x -
              a * ContourC1Space.toBCF γ Z (x + (τ : ContourCircle))) =
            a * (τ⁻¹ • (ContourC1Space.toBCF γ Z x -
              ContourC1Space.toBCF γ Z (x + (τ : ContourCircle))))
          rw [Complex.real_smul, Complex.real_smul]
          ring }
    1 (fun Z => by simpa only [one_mul] using norm_contourNormalizedChord_le hγ Z τ)

@[simp] theorem contourComplexNormalizedChordCLM_apply (hγ : 0 < (γ : ℝ))
    (τ : ℝ) (Z : ContourC1Space γ) :
    contourComplexNormalizedChordCLM hγ τ Z = contourNormalizedChord hγ Z τ := rfl

/-- The actual short-chord lower bound also covers the completed value
at zero, where the normalized chord is the negative actual derivative. -/
theorem norm_contourComplexNormalizedChord_lower (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hZ : ContourC1Space.HasChordArcLower Z c)
    (τ : ℝ) (hτπ : |τ| ≤ Real.pi) (x : ContourCircle) :
    c ≤ ‖contourNormalizedChord hγ Z τ x‖ := by
  by_cases hτ : τ = 0
  · subst τ
    simpa only [contourNormalizedChord_apply, contourNormalizedChordFunction,
      if_pos, norm_neg] using contourC1_derivative_norm_lower Z hZ x
  · exact norm_contourNormalizedChord_lower hγ Z hτ (fun θ => hZ θ τ hτπ) x

def contourComplexNormalizedQuotient (hγ : 0 < (γ : ℝ)) (τ : ℝ)
    (Z : ContourC1Space γ) : ContourHolderSpace γ :=
  HolderFunctionSpace.pointwiseMul
    (contourHolderShift (ContourC1Space.derivative γ Z) τ)
    (HolderFunctionSpace.complexReciprocal γ (contourNormalizedChord hγ Z τ))

theorem contourComplexNormalizedQuotient_apply (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (τ : ℝ) (hτπ : |τ| ≤ Real.pi) (θ : ℝ) :
    contourComplexNormalizedQuotient hγ τ Z (θ : ContourCircle) =
      deriv (ContourC1Space.lift γ Z) (θ + τ) /
        contourNormalizedChord hγ Z τ (θ : ContourCircle) := by
  rw [contourComplexNormalizedQuotient, HolderFunctionSpace.pointwiseMul_apply,
    HolderFunctionSpace.complexReciprocal_apply _ hc
      (norm_contourComplexNormalizedChord_lower hγ Z hZ τ hτπ), div_eq_mul_inv]
  simp only [contourHolderShift_apply, ContourC1Space.deriv_lift, AddCircle.coe_add]

/-- Actual Banach-input complex analyticity of the fixed-parameter
normalized Cauchy quotient, including the completed parameter zero. -/
theorem analyticAt_contourComplexNormalizedQuotient (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (τ : ℝ) (hτπ : |τ| ≤ Real.pi) :
    AnalyticAt ℂ (contourComplexNormalizedQuotient hγ τ) Z := by
  have ha : AnalyticAt ℂ (fun W : ContourC1Space γ => contourNormalizedChord hγ W τ) Z :=
    ((contourComplexNormalizedChordCLM hγ τ).analyticAt Z).congr
      (Eventually.of_forall (fun _ => rfl))
  have hi := HolderFunctionSpace.analyticAt_complexReciprocal (contourNormalizedChord hγ Z τ)
    hc (norm_contourComplexNormalizedChord_lower hγ Z hZ τ hτπ)
  have hr : AnalyticAt ℂ (fun W : ContourC1Space γ =>
      HolderFunctionSpace.complexReciprocal γ (contourNormalizedChord hγ W τ)) Z :=
    hi.comp (f := fun W : ContourC1Space γ => contourNormalizedChord hγ W τ) ha
  have hs : AnalyticAt ℂ (fun W : ContourC1Space γ =>
      contourHolderShift (ContourC1Space.derivative γ W) τ) Z :=
    (((contourComplexHolderShiftCLM γ τ).comp (ContourC1Space.complexDerivative γ)).analyticAt Z).congr
      (Eventually.of_forall (fun _ => rfl))
  have hp := hs.prod hr
  exact (((HolderFunctionSpace.complexPointwiseMulCLM (X := ContourCircle) γ).analyticAt_bilinear
    (contourHolderShift (ContourC1Space.derivative γ Z) τ,
      HolderFunctionSpace.complexReciprocal γ (contourNormalizedChord hγ Z τ))).comp
      (f := fun W : ContourC1Space γ =>
        (contourHolderShift (ContourC1Space.derivative γ W) τ,
          HolderFunctionSpace.complexReciprocal γ (contourNormalizedChord hγ W τ))) hp).congr
            (Eventually.of_forall (fun _ => rfl))

end Euler2D

end
