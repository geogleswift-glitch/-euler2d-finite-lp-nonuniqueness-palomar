module

public import RequestProject.Euler.ContourJointSpace
public import RequestProject.Euler.ContourComplexNormalizedChord
public import RequestProject.Euler.ContourSmoothDividedChord

/-! Actual joint Hölder normalized chords.  Integrals are ordinary
complex integrals at each parameter, and joint Hölder bounds are proved
before constructing elements of the Banach space. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

variable {γ : ℝ≥0}

def contourJointLiftConstant (γ : ℝ≥0) : ℝ := 1 + (2 : ℝ) ^ (γ : ℝ)

theorem contourJointLiftConstant_nonneg (γ : ℝ≥0) : 0 ≤ contourJointLiftConstant γ := by
  unfold contourJointLiftConstant
  positivity

def contourJointShiftPoint (u : ℝ) (p : ContourJointParameter) : ContourCircle :=
  p.1 + ((u * (p.2 : ℝ) : ℝ) : ContourCircle)

theorem dist_contourCircle_coe_le (a b : ℝ) :
    dist (a : ContourCircle) (b : ContourCircle) ≤ |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * Real.pi)) (m := a - b))

theorem dist_contourJointShiftPoint_le (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (p q : ContourJointParameter) :
    dist (contourJointShiftPoint u p) (contourJointShiftPoint u q) ≤ 2 * dist p q := by
  have h₁ : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h₂ : |(p.2 : ℝ) - (q.2 : ℝ)| ≤ dist p q := by
    rw [Prod.dist_eq]
    simpa only [Subtype.dist_eq, Real.dist_eq] using (le_max_right (dist p.1 q.1) (dist p.2 q.2))
  have hm : dist (((u * (p.2 : ℝ) : ℝ)) : ContourCircle)
      (((u * (q.2 : ℝ) : ℝ)) : ContourCircle) ≤ dist p q := by
    calc
      _ ≤ |u * (p.2 : ℝ) - u * (q.2 : ℝ)| := dist_contourCircle_coe_le _ _
      _ = u * |(p.2 : ℝ) - (q.2 : ℝ)| := by rw [← mul_sub, abs_mul, abs_of_nonneg hu.1]
      _ ≤ 1 * dist p q := mul_le_mul hu.2 h₂ (abs_nonneg _) (by norm_num)
      _ = dist p q := one_mul _
  calc
    _ ≤ dist (p.1 + (((u * (p.2 : ℝ) : ℝ)) : ContourCircle))
        (q.1 + (((u * (p.2 : ℝ) : ℝ)) : ContourCircle)) +
        dist (q.1 + (((u * (p.2 : ℝ) : ℝ)) : ContourCircle))
          (q.1 + (((u * (q.2 : ℝ) : ℝ)) : ContourCircle)) := dist_triangle _ _ _
    _ = dist p.1 q.1 + dist (((u * (p.2 : ℝ) : ℝ)) : ContourCircle)
        (((u * (q.2 : ℝ) : ℝ)) : ContourCircle) := by rw [dist_add_right, dist_add_left]
    _ ≤ dist p q + dist p q := add_le_add h₁ hm
    _ = 2 * dist p q := by ring

theorem norm_contourJointShift_sub_le (f : ContourHolderSpace γ) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (p q : ContourJointParameter) :
    ‖f (contourJointShiftPoint u p) - f (contourJointShiftPoint u q)‖ ≤
      contourJointLiftConstant γ * ‖f‖ * dist p q ^ (γ : ℝ) := by
  calc
    _ ≤ ‖f‖ * dist (contourJointShiftPoint u p) (contourJointShiftPoint u q) ^ (γ : ℝ) :=
      HolderFunctionSpace.norm_sub_le_holder f _ _
    _ ≤ ‖f‖ * (2 * dist p q) ^ (γ : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (dist_contourJointShiftPoint_le u hu p q) γ.coe_nonneg)
        (norm_nonneg f)
    _ = (2 : ℝ) ^ (γ : ℝ) * ‖f‖ * dist p q ^ (γ : ℝ) := by
      rw [Real.mul_rpow (by norm_num) dist_nonneg]
      ring
    _ ≤ _ := by
      unfold contourJointLiftConstant
      nlinarith [mul_nonneg (norm_nonneg f) (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist p q) (γ : ℝ))]

theorem contourJoint_holderWith_of_norm_bound {C : ℝ} (hC : 0 ≤ C)
    {f : ContourJointParameter → ℂ}
    (hf : ∀ p q, ‖f p - f q‖ ≤ C * dist p q ^ (γ : ℝ)) :
    HolderWith (⟨C, hC⟩ : ℝ≥0) γ f := by
  intro p q
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f p) (f q) ≤ C * dist p q ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using hf p q
  exact_mod_cast hb

def contourJointHolderOfBound (hγ : 0 < (γ : ℝ)) (f : ContourJointParameter → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ p q, ‖f p - f q‖ ≤ C * dist p q ^ (γ : ℝ)) : ContourJointHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder
    (BoundedContinuousFunction.mkOfCompact
      ⟨f, (contourJoint_holderWith_of_norm_bound hC hf).continuous (by exact_mod_cast hγ)⟩)
    (contourJoint_holderWith_of_norm_bound hC hf).memHolder

theorem norm_contourJointHolderOfBound_le (hγ : 0 < (γ : ℝ))
    (f : ContourJointParameter → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ p q, ‖f p - f q‖ ≤ C * dist p q ^ (γ : ℝ))
    (hs : ∀ p, ‖f p‖ ≤ C) : ‖contourJointHolderOfBound hγ f hC hf‖ ≤ C := by
  exact HolderFunctionSpace.norm_le_of_pointwise_holder_bounds _ hs
    (contourJoint_holderWith_of_norm_bound hC hf)

def contourJointAverageFunction (f : ContourHolderSpace γ) (p : ContourJointParameter) : ℂ :=
  ∫ u in (0 : ℝ)..1, f (contourJointShiftPoint u p)

theorem continuous_contourJointShift_in_u (f : ContourHolderSpace γ) (p : ContourJointParameter) :
    Continuous (fun u : ℝ => f (contourJointShiftPoint u p)) := by
  exact (HolderFunctionSpace.toBCF γ f).continuous.comp
    (continuous_const.add ((AddCircle.continuous_mk' (2 * Real.pi)).comp
      (continuous_id.mul continuous_const)))

theorem intervalIntegrable_contourJointShift (f : ContourHolderSpace γ) (p : ContourJointParameter) :
    IntervalIntegrable (fun u : ℝ => f (contourJointShiftPoint u p)) volume 0 1 :=
  (continuous_contourJointShift_in_u f p).intervalIntegrable _ _

theorem norm_contourJointAverageFunction_le (f : ContourHolderSpace γ) (p : ContourJointParameter) :
    ‖contourJointAverageFunction f p‖ ≤ ‖f‖ := by
  simpa only [sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (fun u _ => HolderFunctionSpace.norm_eval_le f (contourJointShiftPoint u p)))

theorem norm_contourJointAverageFunction_sub_le (f : ContourHolderSpace γ)
    (p q : ContourJointParameter) :
    ‖contourJointAverageFunction f p - contourJointAverageFunction f q‖ ≤
      contourJointLiftConstant γ * ‖f‖ * dist p q ^ (γ : ℝ) := by
  rw [contourJointAverageFunction, contourJointAverageFunction,
    ← intervalIntegral.integral_sub (intervalIntegrable_contourJointShift f p)
      (intervalIntegrable_contourJointShift f q)]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu =>
    norm_contourJointShift_sub_le f u (by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact ⟨hu.1.le, hu.2⟩) p q)).trans_eq
  simp only [sub_zero, abs_one, mul_one]

def contourJointAverageHolder (hγ : 0 < (γ : ℝ)) (f : ContourHolderSpace γ) :
    ContourJointHolderSpace γ :=
  contourJointHolderOfBound hγ (contourJointAverageFunction f)
    (mul_nonneg (contourJointLiftConstant_nonneg γ) (norm_nonneg f))
    (norm_contourJointAverageFunction_sub_le f)

@[simp] theorem contourJointAverageHolder_apply (hγ : 0 < (γ : ℝ))
    (f : ContourHolderSpace γ) (p : ContourJointParameter) :
    contourJointAverageHolder hγ f p = contourJointAverageFunction f p := rfl

theorem norm_contourJointAverageHolder_le (hγ : 0 < (γ : ℝ)) (f : ContourHolderSpace γ) :
    ‖contourJointAverageHolder hγ f‖ ≤ contourJointLiftConstant γ * ‖f‖ := by
  apply norm_contourJointHolderOfBound_le
  intro p
  calc
    _ ≤ ‖f‖ := norm_contourJointAverageFunction_le f p
    _ ≤ _ := by
      unfold contourJointLiftConstant
      nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (γ : ℝ)) (norm_nonneg f)]

def contourJointEndpointHolder (hγ : 0 < (γ : ℝ)) (f : ContourHolderSpace γ) :
    ContourJointHolderSpace γ :=
  contourJointHolderOfBound hγ (fun p => f (contourJointShiftPoint 1 p))
    (mul_nonneg (contourJointLiftConstant_nonneg γ) (norm_nonneg f))
    (norm_contourJointShift_sub_le f 1 ⟨by norm_num, by norm_num⟩)

@[simp] theorem contourJointEndpointHolder_apply (hγ : 0 < (γ : ℝ))
    (f : ContourHolderSpace γ) (p : ContourJointParameter) :
    contourJointEndpointHolder hγ f p = f (p.1 + ((p.2 : ℝ) : ContourCircle)) := by
  change f (p.1 + (((1 : ℝ) * (p.2 : ℝ) : ℝ) : ContourCircle)) = _
  rw [one_mul]

theorem norm_contourJointEndpointHolder_le (hγ : 0 < (γ : ℝ)) (f : ContourHolderSpace γ) :
    ‖contourJointEndpointHolder hγ f‖ ≤ contourJointLiftConstant γ * ‖f‖ := by
  apply norm_contourJointHolderOfBound_le
  intro p
  calc
    _ ≤ ‖f‖ := HolderFunctionSpace.norm_eval_le f _
    _ ≤ _ := by
      unfold contourJointLiftConstant
      nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (γ : ℝ)) (norm_nonneg f)]

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower ContourC1Space.complexScalarNormedSpace
  ContourC1Space.complexScalarTower

def contourJointAverageCLM (hγ : 0 < (γ : ℝ)) :
    ContourHolderSpace γ →L[ℂ] ContourJointHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := contourJointAverageHolder hγ
      map_add' := by
        intro f g
        apply HolderFunctionSpace.ext
        intro p
        change (∫ u in (0 : ℝ)..1, (f + g) (contourJointShiftPoint u p)) = _
        simp only [HolderFunctionSpace.add_apply]
        exact intervalIntegral.integral_add (intervalIntegrable_contourJointShift f p)
          (intervalIntegrable_contourJointShift g p)
      map_smul' := by
        intro a f
        apply HolderFunctionSpace.ext
        intro p
        change (∫ u in (0 : ℝ)..1, a * f (contourJointShiftPoint u p)) =
          a * (∫ u in (0 : ℝ)..1, f (contourJointShiftPoint u p))
        exact intervalIntegral.integral_const_mul a _ }
    (contourJointLiftConstant γ) (norm_contourJointAverageHolder_le hγ)

def contourJointEndpointCLM (hγ : 0 < (γ : ℝ)) :
    ContourHolderSpace γ →L[ℂ] ContourJointHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := contourJointEndpointHolder hγ
      map_add' := by
        intro f g
        apply HolderFunctionSpace.ext
        intro p
        rfl
      map_smul' := by
        intro a f
        apply HolderFunctionSpace.ext
        intro p
        rfl }
    (contourJointLiftConstant γ) (norm_contourJointEndpointHolder_le hγ)

/-- The negative FTC average, with the same orientation as the genuine
Cauchy denominator `Z θ - Z (θ + τ)`. -/
def contourJointNormalizedChordCLM (hγ : 0 < (γ : ℝ)) :
    ContourC1Space γ →L[ℂ] ContourJointHolderSpace γ :=
  -((contourJointAverageCLM hγ).comp (ContourC1Space.complexDerivative γ))

def contourJointDerivativeShiftCLM (hγ : 0 < (γ : ℝ)) :
    ContourC1Space γ →L[ℂ] ContourJointHolderSpace γ :=
  (contourJointEndpointCLM hγ).comp (ContourC1Space.complexDerivative γ)

theorem contourJointNormalizedChordCLM_coe (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ)
    (θ : ℝ) (τ : ContourIncrementInterval) :
    contourJointNormalizedChordCLM hγ Z ((θ : ContourCircle), τ) =
      -smoothContourNormalizedChord (ContourC1Space.lift γ Z) θ τ := by
  change -(∫ u in (0 : ℝ)..1,
    ContourC1Space.derivative γ Z (contourJointShiftPoint u ((θ : ContourCircle), τ))) = _
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp only [smoothContourNormalizedChord, ContourC1Space.deriv_lift,
    contourJointShiftPoint, AddCircle.coe_add]

/-- Exact identification with the original actual completed divided chord. -/
theorem contourJointNormalizedChordCLM_apply (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ)
    (p : ContourJointParameter) :
    contourJointNormalizedChordCLM hγ Z p = contourNormalizedChord hγ Z p.2 p.1 := by
  obtain ⟨x, τ⟩ := p
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourJointNormalizedChordCLM_coe]
  by_cases hτ : (τ : ℝ) = 0
  · simp only [hτ, smoothContourNormalizedChord_zero, ContourC1Space.deriv_lift,
      contourNormalizedChord_apply, contourNormalizedChordFunction, if_pos]
  · rw [smoothContourNormalizedChord_eq_div (ContourC1Space.contDiff_lift Z) θ hτ,
      contourNormalizedChord_apply, contourNormalizedChordFunction_coe Z hτ θ,
      Complex.real_smul]
    push_cast
    ring

theorem contourJointDerivativeShiftCLM_apply (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ)
    (p : ContourJointParameter) :
    contourJointDerivativeShiftCLM hγ Z p =
      ContourC1Space.derivative γ Z (p.1 + ((p.2 : ℝ) : ContourCircle)) :=
  contourJointEndpointHolder_apply hγ _ p

theorem norm_contourJointNormalizedChord_lower (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hZ : ContourC1Space.HasChordArcLower Z c)
    (p : ContourJointParameter) : c ≤ ‖contourJointNormalizedChordCLM hγ Z p‖ := by
  rw [contourJointNormalizedChordCLM_apply]
  exact norm_contourComplexNormalizedChord_lower hγ Z hZ p.2 (abs_le.mpr p.2.property) p.1

def contourJointNormalizedQuotient (hγ : 0 < (γ : ℝ)) (Z : ContourC1Space γ) :
    ContourJointHolderSpace γ :=
  HolderFunctionSpace.pointwiseMul (contourJointDerivativeShiftCLM hγ Z)
    (HolderFunctionSpace.complexReciprocal γ (contourJointNormalizedChordCLM hγ Z))

theorem contourJointNormalizedQuotient_apply (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (p : ContourJointParameter) :
    contourJointNormalizedQuotient hγ Z p =
      ContourC1Space.derivative γ Z (p.1 + ((p.2 : ℝ) : ContourCircle)) /
        contourNormalizedChord hγ Z p.2 p.1 := by
  rw [contourJointNormalizedQuotient, HolderFunctionSpace.pointwiseMul_apply,
    HolderFunctionSpace.complexReciprocal_apply _ hc (norm_contourJointNormalizedChord_lower hγ Z hZ),
    contourJointDerivativeShiftCLM_apply, contourJointNormalizedChordCLM_apply,
    div_eq_mul_inv]

theorem contourJointNormalizedQuotient_zero (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (x : ContourCircle) :
    contourJointSample (contourJointNormalizedQuotient hγ Z) x 0 = -1 := by
  rw [contourJointSample_zero, contourJointNormalizedQuotient_apply hγ Z hc hZ]
  have hd : ContourC1Space.derivative γ Z x ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le (contourC1_derivative_norm_lower Z hZ x))
  simp only [contourZeroIncrement, AddCircle.coe_zero, add_zero,
    contourNormalizedChord_apply, contourNormalizedChordFunction, if_pos,
    div_neg, div_self hd]

/-- Complex analyticity in the actual joint Hölder norm, as an ordinary
composition of proved continuous linear and bilinear maps with the actual
Banach-algebra inverse. -/
theorem analyticAt_contourJointNormalizedQuotient (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) :
    AnalyticAt ℂ (contourJointNormalizedQuotient hγ) Z := by
  have ha := (contourJointNormalizedChordCLM hγ).analyticAt Z
  have hi := HolderFunctionSpace.analyticAt_complexReciprocal (contourJointNormalizedChordCLM hγ Z)
    hc (norm_contourJointNormalizedChord_lower hγ Z hZ)
  have hr : AnalyticAt ℂ (fun W : ContourC1Space γ =>
      HolderFunctionSpace.complexReciprocal γ (contourJointNormalizedChordCLM hγ W)) Z :=
    hi.comp (f := fun W : ContourC1Space γ => contourJointNormalizedChordCLM hγ W) ha
  have hs := (contourJointDerivativeShiftCLM hγ).analyticAt Z
  have hp := hs.prod hr
  exact (((HolderFunctionSpace.complexPointwiseMulCLM (X := ContourJointParameter) γ).analyticAt_bilinear
    (contourJointDerivativeShiftCLM hγ Z,
      HolderFunctionSpace.complexReciprocal γ (contourJointNormalizedChordCLM hγ Z))).comp
      (f := fun W : ContourC1Space γ =>
        (contourJointDerivativeShiftCLM hγ W,
          HolderFunctionSpace.complexReciprocal γ (contourJointNormalizedChordCLM hγ W))) hp).congr
            (Eventually.of_forall (fun _ => rfl))

end Euler2D

end
