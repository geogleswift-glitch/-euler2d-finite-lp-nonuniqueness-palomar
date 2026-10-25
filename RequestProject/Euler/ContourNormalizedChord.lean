module

public import RequestProject.Euler.ContourCauchyRemainderHolder
public import RequestProject.Euler.ContourHolderInverseContinuity

/-! # Genuine Hölder normalized chords of a contour

The divided chord is constructed from the actual circle function. Its
Hölder estimates follow from the true derivative and the mean value
theorem, without an integral in the full Hölder space.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

theorem contour_holderWith_of_norm_bound {γ : ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    {f : ContourCircle → ℂ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) :
    HolderWith (⟨C, hC⟩ : ℝ≥0) γ f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using hf x y
  exact_mod_cast hb

theorem norm_contourHolder_le_of_bounds {γ : ℝ≥0} (f : ContourHolderSpace γ)
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ x, ‖f x‖ ≤ C)
    (hh : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) : ‖f‖ ≤ C :=
  HolderFunctionSpace.norm_le_of_pointwise_holder_bounds f (C := ⟨C, hC⟩) hs
    (contour_holderWith_of_norm_bound hC hh)

def contourHolderShift {γ : ℝ≥0} (f : ContourHolderSpace γ) (τ : ℝ) :
    ContourHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => f (x + (τ : ContourCircle)),
        (HolderFunctionSpace.toBCF γ f).continuous.comp (continuous_id.add continuous_const)⟩)
    (contour_holderWith_of_norm_bound (norm_nonneg f) (fun x y => by
      simpa only [dist_add_right] using
        HolderFunctionSpace.norm_sub_le_holder f (x + (τ : ContourCircle))
          (y + (τ : ContourCircle)))).memHolder

@[simp] theorem contourHolderShift_apply {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (τ : ℝ) (x : ContourCircle) : contourHolderShift f τ x = f (x + (τ : ContourCircle)) := rfl

theorem norm_contourHolderShift_le {γ : ℝ≥0} (f : ContourHolderSpace γ) (τ : ℝ) :
    ‖contourHolderShift f τ‖ ≤ ‖f‖ := by
  apply norm_contourHolder_le_of_bounds _ (norm_nonneg f)
  · intro x
    exact HolderFunctionSpace.norm_eval_le f _
  · intro x y
    simpa only [contourHolderShift_apply, dist_add_right] using
      HolderFunctionSpace.norm_sub_le_holder f (x + (τ : ContourCircle))
        (y + (τ : ContourCircle))

theorem contourHolderShift_sub {γ : ℝ≥0} (f g : ContourHolderSpace γ) (τ : ℝ) :
    contourHolderShift (f - g) τ = contourHolderShift f τ - contourHolderShift g τ := by
  apply HolderFunctionSpace.ext
  intro x
  rfl

/-- The true normalized chord, completed at zero by its actual limit. -/
def contourNormalizedChordFunction {γ : ℝ≥0} (Z : ContourC1Space γ)
    (τ : ℝ) (x : ContourCircle) : ℂ :=
  if τ = 0 then -ContourC1Space.derivative γ Z x else
    τ⁻¹ • (ContourC1Space.toBCF γ Z x -
      ContourC1Space.toBCF γ Z (x + (τ : ContourCircle)))

theorem contourNormalizedChordFunction_coe {γ : ℝ≥0} (Z : ContourC1Space γ)
    {τ : ℝ} (hτ : τ ≠ 0) (θ : ℝ) :
    contourNormalizedChordFunction Z τ (θ : ContourCircle) =
      τ⁻¹ • (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)) := by
  simp only [contourNormalizedChordFunction, if_neg hτ, ContourC1Space.lift, AddCircle.coe_add]

theorem norm_contourNormalizedChordFunction_le {γ : ℝ≥0}
    (Z : ContourC1Space γ) (τ : ℝ) (x : ContourCircle) :
    ‖contourNormalizedChordFunction Z τ x‖ ≤ ‖Z‖ := by
  by_cases hτ : τ = 0
  · subst τ
    simpa only [contourNormalizedChordFunction, if_pos, norm_neg] using
      ContourC1Space.norm_derivativeEval_le Z x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourNormalizedChordFunction_coe Z hτ, norm_smul, Real.norm_eq_abs, abs_inv]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ uIcc θ (θ + τ)) => (ContourC1Space.hasDerivAt_lift Z s).hasDerivWithinAt)
    (fun s (_ : s ∈ uIcc θ (θ + τ)) => ContourC1Space.norm_derivativeEval_le Z (s : ContourCircle))
    (convex_uIcc θ (θ + τ)) left_mem_uIcc right_mem_uIcc
  have hb : ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ ≤ ‖Z‖ * |τ| := by
    simpa only [norm_sub_rev, add_sub_cancel_left, Real.norm_eq_abs] using hm
  calc
    _ ≤ |τ|⁻¹ * (‖Z‖ * |τ|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = ‖Z‖ := by field_simp

theorem norm_contourNormalizedChordFunction_sub_le {γ : ℝ≥0}
    (Z : ContourC1Space γ) (τ : ℝ) (x y : ContourCircle) :
    ‖contourNormalizedChordFunction Z τ x - contourNormalizedChordFunction Z τ y‖ ≤
      ‖Z‖ * dist x y ^ (γ : ℝ) := by
  by_cases hτ : τ = 0
  · subst τ
    simpa only [contourNormalizedChordFunction, if_pos, neg_sub_neg, norm_sub_rev] using
      ContourC1Space.norm_derivative_sub_le_holder Z x y
  obtain ⟨θ, η, hθ, hη, _, hdist⟩ := exists_short_contour_representatives x y
  rw [← hθ, ← hη, contourNormalizedChordFunction_coe Z hτ,
    contourNormalizedChordFunction_coe Z hτ, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_inv]
  have hb := norm_contour_chord_parameter_sub_le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) θ η τ
  calc
    _ ≤ |τ|⁻¹ * ((‖Z‖ * |θ - η| ^ (γ : ℝ)) * |τ|) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = ‖Z‖ * dist (θ : ContourCircle) (η : ContourCircle) ^ (γ : ℝ) := by
      rw [hθ, hη, hdist]
      field_simp

def contourNormalizedChord {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) (τ : ℝ) : ContourHolderSpace γ :=
  contourHolderOfMemHolder (by exact_mod_cast hγ) (contourNormalizedChordFunction Z τ)
    (contour_holderWith_of_norm_bound (norm_nonneg Z)
      (norm_contourNormalizedChordFunction_sub_le Z τ)).memHolder

@[simp] theorem contourNormalizedChord_apply {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) (τ : ℝ) (x : ContourCircle) :
    contourNormalizedChord hγ Z τ x = contourNormalizedChordFunction Z τ x := rfl

theorem norm_contourNormalizedChord_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) (τ : ℝ) : ‖contourNormalizedChord hγ Z τ‖ ≤ ‖Z‖ :=
  norm_contourHolder_le_of_bounds _ (norm_nonneg Z)
    (norm_contourNormalizedChordFunction_le Z τ)
    (norm_contourNormalizedChordFunction_sub_le Z τ)

theorem contourNormalizedChord_sub {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z W : ContourC1Space γ) (τ : ℝ) :
    contourNormalizedChord hγ (Z - W) τ =
      contourNormalizedChord hγ Z τ - contourNormalizedChord hγ W τ := by
  apply HolderFunctionSpace.ext
  intro x
  by_cases hτ : τ = 0
  · simp only [contourNormalizedChord_apply, contourNormalizedChordFunction, if_pos hτ,
      map_sub, HolderFunctionSpace.sub_apply]
    abel
  · simp only [contourNormalizedChord_apply, contourNormalizedChordFunction, if_neg hτ,
      map_sub, BoundedContinuousFunction.sub_apply, HolderFunctionSpace.sub_apply]
    rw [← smul_sub]
    congr 1
    abel

theorem norm_contourNormalizedChord_sub_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z W : ContourC1Space γ) (τ : ℝ) :
    ‖contourNormalizedChord hγ Z τ - contourNormalizedChord hγ W τ‖ ≤ ‖Z - W‖ := by
  rw [← contourNormalizedChord_sub]
  exact norm_contourNormalizedChord_le hγ (Z - W) τ

theorem norm_contourNormalizedChord_error_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {τ : ℝ} (hτ : τ ≠ 0) (θ : ℝ) :
    ‖deriv (ContourC1Space.lift γ Z) (θ + τ) +
      contourNormalizedChord hγ Z τ (θ : ContourCircle)‖ ≤ ‖Z‖ * |τ| ^ (γ : ℝ) := by
  have hb := norm_dividedDifference_sub_derivative γ.coe_nonneg (norm_nonneg Z)
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) (θ + τ) (τ := -τ) (neg_ne_zero.mpr hτ)
  rw [contourNormalizedChord_apply, contourNormalizedChordFunction_coe Z hτ]
  have he : (-τ)⁻¹ • (ContourC1Space.lift γ Z ((θ + τ) + -τ) -
      ContourC1Space.lift γ Z (θ + τ)) - deriv (ContourC1Space.lift γ Z) (θ + τ) =
      -(deriv (ContourC1Space.lift γ Z) (θ + τ) +
        τ⁻¹ • (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ))) := by
    simp only [add_neg_cancel_right, inv_neg, neg_smul]
    abel
  simpa only [he, norm_neg, abs_neg] using hb

end Euler2D

end
