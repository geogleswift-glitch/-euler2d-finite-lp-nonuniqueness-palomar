module

public import RequestProject.Euler.ContourNormalizedChord
public import RequestProject.Euler.ContourComplexHolderSpace
public import RequestProject.Euler.AreaChart

/-! The genuine rotation/reparametrization is a real linear isometry
of the actual C¹ Hölder derivative graph, with its unchanged norm. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

variable {γ : ℝ≥0}

def contourRotationBCF (b : ℝ) (f : ContourCircle →ᵇ ℂ) : ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Complex.exp ((b : ℂ) * Complex.I) * f (x - (b : ContourCircle)),
      continuous_const.mul (f.continuous.comp (continuous_id.sub continuous_const))⟩

theorem norm_contourRotationBCF_le (b : ℝ) (f : ContourCircle →ᵇ ℂ) :
    ‖contourRotationBCF b f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖Complex.exp ((b : ℂ) * Complex.I) * f (x - (b : ContourCircle))‖ ≤ ‖f‖
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact f.norm_coe_le_norm _

def contourRotationHolder (b : ℝ) (f : ContourHolderSpace γ) : ContourHolderSpace γ :=
  HolderFunctionSpace.valueMulOperator γ (Complex.exp ((b : ℂ) * Complex.I)) (contourHolderShift f (-b))

@[simp] theorem contourRotationHolder_apply (b : ℝ) (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourRotationHolder b f x = Complex.exp ((b : ℂ) * Complex.I) * f (x - (b : ContourCircle)) := by
  simp only [contourRotationHolder, HolderFunctionSpace.valueMulOperator_apply,
    contourHolderShift_apply, AddCircle.coe_neg, sub_eq_add_neg]

theorem norm_contourRotationHolder_le (b : ℝ) (f : ContourHolderSpace γ) :
    ‖contourRotationHolder b f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖Complex.exp ((b : ℂ) * Complex.I)‖ * ‖contourHolderShift f (-b)‖ :=
      HolderFunctionSpace.norm_valueMulOperator_apply_le _ _
    _ = ‖contourHolderShift f (-b)‖ := by rw [Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ ‖f‖ := norm_contourHolderShift_le f (-b)

def contourRotationC1 (b : ℝ) (Z : ContourC1Space γ) : ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt (contourRotationBCF b (ContourC1Space.toBCF γ Z))
    (contourRotationHolder b (ContourC1Space.derivative γ Z)) (by
      intro θ
      have hd := ((ContourC1Space.hasDerivAt_lift Z (θ - b)).scomp θ
        ((hasDerivAt_id θ).sub_const b)).const_mul (Complex.exp ((b : ℂ) * Complex.I))
      simpa only [one_smul, ContourC1Space.lift, contourRotationBCF,
        BoundedContinuousFunction.mkOfCompact_apply, contourRotationHolder_apply,
        AddCircle.coe_sub] using hd)

theorem contourRotationC1_lift (b : ℝ) (Z : ContourC1Space γ) :
    ContourC1Space.lift γ (contourRotationC1 b Z) = rotShift b (ContourC1Space.lift γ Z) := by
  funext θ
  change Complex.exp ((b : ℂ) * Complex.I) * ContourC1Space.toBCF γ Z
      ((θ : ContourCircle) - (b : ContourCircle)) = _
  simp only [rotShift, ContourC1Space.lift, AddCircle.coe_sub]

@[simp] theorem derivative_contourRotationC1 (b : ℝ) (Z : ContourC1Space γ) :
    ContourC1Space.derivative γ (contourRotationC1 b Z) =
      contourRotationHolder b (ContourC1Space.derivative γ Z) := rfl

theorem norm_contourRotationC1_le (b : ℝ) (Z : ContourC1Space γ) :
    ‖contourRotationC1 b Z‖ ≤ ‖Z‖ := by
  change max ‖contourRotationBCF b (ContourC1Space.toBCF γ Z)‖
    ‖contourRotationHolder b (ContourC1Space.derivative γ Z)‖ ≤
      max ‖ContourC1Space.toBCF γ Z‖ ‖ContourC1Space.derivative γ Z‖
  exact max_le_max (norm_contourRotationBCF_le _ _) (norm_contourRotationHolder_le _ _)

def contourRotationC1CLM (γ : ℝ≥0) (b : ℝ) : ContourC1Space γ →L[ℝ] ContourC1Space γ :=
  LinearMap.mkContinuous
    { toFun := contourRotationC1 b
      map_add' := by
        intro Z W
        apply ContourC1Space.ext
        intro x
        change Complex.exp ((b : ℂ) * Complex.I) *
          (ContourC1Space.toBCF γ Z (x - (b : ContourCircle)) +
            ContourC1Space.toBCF γ W (x - (b : ContourCircle))) = _
        exact mul_add _ _ _
      map_smul' := by
        intro r Z
        apply ContourC1Space.ext
        intro x
        change Complex.exp ((b : ℂ) * Complex.I) *
          (r • ContourC1Space.toBCF γ Z (x - (b : ContourCircle))) =
            r • (Complex.exp ((b : ℂ) * Complex.I) * ContourC1Space.toBCF γ Z (x - (b : ContourCircle)))
        rw [Complex.real_smul, Complex.real_smul]
        ring }
    1 (fun Z => by simpa only [one_mul] using norm_contourRotationC1_le b Z)

@[simp] theorem contourRotationC1_zero (Z : ContourC1Space γ) : contourRotationC1 0 Z = Z := by
  apply ContourC1Space.ext
  intro x
  change Complex.exp (((0 : ℝ) : ℂ) * Complex.I) *
    ContourC1Space.toBCF γ Z (x - ((0 : ℝ) : ContourCircle)) = _
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, AddCircle.coe_zero, sub_zero]

theorem contourRotationC1_add (b c : ℝ) (Z : ContourC1Space γ) :
    contourRotationC1 b (contourRotationC1 c Z) = contourRotationC1 (b + c) Z := by
  apply ContourC1Space.ext
  intro x
  change Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp ((c : ℂ) * Complex.I) *
      ContourC1Space.toBCF γ Z ((x - (b : ContourCircle)) - (c : ContourCircle))) =
    Complex.exp (((b + c : ℝ) : ℂ) * Complex.I) *
      ContourC1Space.toBCF γ Z (x - ((b + c : ℝ) : ContourCircle))
  rw [← mul_assoc, ← Complex.exp_add]
  have he : (b : ℂ) * Complex.I + (c : ℂ) * Complex.I = ((b + c : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, AddCircle.coe_add, sub_sub]

theorem norm_contourRotationC1 (b : ℝ) (Z : ContourC1Space γ) : ‖contourRotationC1 b Z‖ = ‖Z‖ := by
  apply le_antisymm (norm_contourRotationC1_le b Z)
  have h := norm_contourRotationC1_le (-b) (contourRotationC1 b Z)
  simpa only [contourRotationC1_add, neg_add_cancel, contourRotationC1_zero] using h

def contourRotationC1Isometry (γ : ℝ≥0) (b : ℝ) : ContourC1Space γ ≃ₗᵢ[ℝ] ContourC1Space γ where
  toLinearEquiv :=
    { toLinearMap := (contourRotationC1CLM γ b).toLinearMap
      invFun := contourRotationC1 (-b)
      left_inv := fun Z => by
        change contourRotationC1 (-b) (contourRotationC1 b Z) = Z
        rw [contourRotationC1_add, neg_add_cancel, contourRotationC1_zero]
      right_inv := fun Z => by
        change contourRotationC1 b (contourRotationC1 (-b) Z) = Z
        rw [contourRotationC1_add, add_neg_cancel, contourRotationC1_zero] }
  norm_map' := norm_contourRotationC1 b

theorem contourRotationC1_refCircle (b : ℝ) (Z : ContourC1Space γ) {r : ℝ}
    (href : ContourC1Space.lift γ Z = refCircle r) : contourRotationC1 b Z = Z := by
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ContourC1Space.lift γ (contourRotationC1 b Z) θ = ContourC1Space.lift γ Z θ
  rw [contourRotationC1_lift, href, rotShift_refCircle]

end Euler2D

end
