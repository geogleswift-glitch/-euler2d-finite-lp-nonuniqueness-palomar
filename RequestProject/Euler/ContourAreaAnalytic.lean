module

public import RequestProject.Euler.ContourSmoothEmbedding
public import RequestProject.Euler.ContourEvaluation
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Actual Banach-space area and linear area constraint

The bounded bilinear form is constructed from the genuine contour function,
its genuine derivative, complex conjugation and the actual interval integral.
Its diagonal is exactly the original `loopArea`.  The linear constraint is
also an actual continuous linear map agreeing with the original `ellFun`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open scoped NNReal ENNReal BoundedContinuousFunction ComplexConjugate ContDiff

namespace Euler2D

-- These are the canonical inherited structures.  Naming them avoids a
-- large generic submodule search when the codomain is itself an operator space.
instance (priority := 2000) contourC1Space_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

instance (priority := 2000) contourC1Space_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

instance (priority := 2000) littleContourSpace_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

instance (priority := 2000) littleContourSpace_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) :=
  Submodule.normedSpace (LittleContourSpace γ)

private lemma contourBCF_lift_continuous {E : Type*} [NormedAddCommGroup E]
    (f : ContourCircle →ᵇ E) : Continuous (fun θ : ℝ => f (θ : ContourCircle)) :=
  f.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))

/-- Actual integration over one full parameter period. -/
def contourRealIntegral : (ContourCircle →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ in (0 : ℝ)..2 * Real.pi, f (θ : ContourCircle)
      map_add' := fun f g => by
        exact intervalIntegral.integral_add
          ((contourBCF_lift_continuous f).intervalIntegrable _ _)
          ((contourBCF_lift_continuous g).intervalIntegrable _ _)
      map_smul' := fun c f => intervalIntegral.integral_smul c _ }
    (2 * Real.pi) (fun f => by
      calc
        ‖∫ θ in (0 : ℝ)..2 * Real.pi, f (θ : ContourCircle)‖ ≤
            ‖f‖ * |2 * Real.pi - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => f.norm_coe_le_norm _)
        _ = (2 * Real.pi) * ‖f‖ := by
          rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          ring)

/-- Actual imaginary-part integration as a continuous linear functional. -/
def contourImaginaryIntegral : (ContourCircle →ᵇ ℂ) →L[ℝ] ℝ :=
  contourRealIntegral.comp (Complex.imCLM.compLeftContinuousBounded ContourCircle)

/-- Actual conjugate of the contour function. -/
def contourConjugateValue (γ : ℝ≥0) : ContourC1Space γ →L[ℝ] (ContourCircle →ᵇ ℂ) :=
  (Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ContourCircle).comp
    (ContourC1Space.toBCF γ)

/-- The actual derivative as a bounded continuous function. -/
def contourDerivativeBCF (γ : ℝ≥0) : ContourC1Space γ →L[ℝ] (ContourCircle →ᵇ ℂ) :=
  (HolderFunctionSpace.toBCF γ).comp (ContourC1Space.derivative γ)

/-- The genuine bounded real bilinear area form, including the factor 1/2. -/
def contourAreaForm (γ : ℝ≥0) : ContourC1Space γ →L[ℝ] ContourC1Space γ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.compL ℝ (ContourC1Space γ) (ContourCircle →ᵇ ℂ) ℝ
        contourImaginaryIntegral).comp
      (((ContinuousLinearMap.precompR (ContourC1Space γ)
          (ContinuousLinearMap.mul ℝ (ContourCircle →ᵇ ℂ))).flip
            (contourDerivativeBCF γ)).comp (contourConjugateValue γ)))

theorem contourAreaForm_apply {γ : ℝ≥0} (f g : ContourC1Space γ) :
    contourAreaForm γ f g = (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (ContourC1Space.lift γ f θ) *
        ContourC1Space.derivative γ g (θ : ContourCircle)).im := rfl

theorem contourAreaForm_diagonal {γ : ℝ≥0} (f : ContourC1Space γ) :
    contourAreaForm γ f f = loopArea (ContourC1Space.lift γ f) := by
  rw [contourAreaForm_apply, loopArea]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [ContourC1Space.deriv_lift]

/-- The original actual signed area, viewed as a Banach-space map. -/
def contourArea (γ : ℝ≥0) (f : ContourC1Space γ) : ℝ :=
  loopArea (ContourC1Space.lift γ f)

lemma contourArea_eq_diagonal (γ : ℝ≥0) :
    contourArea γ = fun f => contourAreaForm γ f f :=
  funext (fun f => (contourAreaForm_diagonal f).symm)

theorem analyticAt_contourArea {γ : ℝ≥0} (f : ContourC1Space γ) :
    AnalyticAt ℝ (contourArea γ) f := by
  rw [contourArea_eq_diagonal]
  have hd : AnalyticAt ℝ (fun v : ContourC1Space γ => (v, v)) f :=
    (analyticAt_id : AnalyticAt ℝ (id : ContourC1Space γ → ContourC1Space γ) f).prod
      analyticAt_id
  exact ((contourAreaForm γ).analyticAt_bilinear (f, f)).comp
    (f := fun v : ContourC1Space γ => (v, v)) hd

theorem continuous_contourArea (γ : ℝ≥0) : Continuous (contourArea γ) :=
  continuous_iff_continuousAt.mpr (fun f => (analyticAt_contourArea f).continuousAt)

@[simp] theorem contourArea_zero (γ : ℝ≥0) : contourArea γ 0 = 0 := by
  rw [contourArea_eq_diagonal]
  have hz : contourAreaForm γ (0 : ContourC1Space γ) =
      (0 : ContourC1Space γ →L[ℝ] ℝ) :=
    ContinuousLinearMap.map_zero (contourAreaForm γ)
  exact congrArg (fun L : ContourC1Space γ →L[ℝ] ℝ => L 0) hz

private theorem hasFDerivAt_bilinear_diagonal_zero {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] E →L[ℝ] G) :
    HasFDerivAt (fun f => B f f) (0 : E →L[ℝ] G) 0 := by
  have hd := B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : E)) (hasFDerivAt_id (0 : E))
  have hz : B (0 : E) = (0 : E →L[ℝ] G) := ContinuousLinearMap.map_zero B
  have hD : B.precompR E 0 (ContinuousLinearMap.id ℝ E) +
      B.precompL E (ContinuousLinearMap.id ℝ E) 0 = 0 := by
    ext v
    change B 0 v + B v 0 = 0
    rw [hz]
    exact (zero_add _).trans (ContinuousLinearMap.map_zero (B v))
  simp only [id_eq] at hd
  rw [hD] at hd
  exact hd

theorem hasFDerivAt_contourArea_zero (γ : ℝ≥0) :
    HasFDerivAt (contourArea γ) (0 : ContourC1Space γ →L[ℝ] ℝ) 0 := by
  rw [contourArea_eq_diagonal]
  exact hasFDerivAt_bilinear_diagonal_zero (contourAreaForm γ)

/-- The actual reference circle as a bounded function on the parameter circle. -/
def referenceCircleBCF (r : ℝ) : ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨(periodic_refCircle r).lift, continuous_periodicContourLift (periodic_refCircle r)
      (contDiff_refCircle r).continuous⟩

/-- The actual exponential weight appearing in the original linear constraint. -/
def contourEllWeight : ContourCircle →ᵇ ℂ :=
  Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ContourCircle (referenceCircleBCF 1)

lemma contourEllWeight_lift (θ : ℝ) :
    contourEllWeight (θ : ContourCircle) = Complex.exp (-(θ * I)) := by
  change conj (refCircle 1 θ) = Complex.exp (-(θ * I))
  simp only [refCircle, Complex.ofReal_one, one_mul, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- The original linear area constraint as an actual continuous linear map. -/
def contourEllCLM (γ : ℝ≥0) (r : ℝ) : ContourC1Space γ →L[ℝ] ℝ :=
  r • (contourRealIntegral.comp
    ((Complex.reCLM.compLeftContinuousBounded ContourCircle).comp
      ((ContinuousLinearMap.mul ℝ (ContourCircle →ᵇ ℂ) contourEllWeight).comp
        (ContourC1Space.toBCF γ))))

theorem contourEllCLM_eq_ellFun {γ : ℝ≥0} (r : ℝ) (f : ContourC1Space γ) :
    contourEllCLM γ r f = ellFun r (ContourC1Space.lift γ f) := by
  change r * (∫ θ in (0 : ℝ)..2 * Real.pi,
    (contourEllWeight (θ : ContourCircle) * ContourC1Space.lift γ f θ).re) = _
  simp only [contourEllWeight_lift, ellFun]

theorem isClosed_contourEll_kernel (γ : ℝ≥0) (r : ℝ) :
    IsClosed ((contourEllCLM γ r).ker : Set (ContourC1Space γ)) :=
  isClosed_eq (contourEllCLM γ r).continuous continuous_const

/-- The same genuine area form on the actual little contour Banach space. -/
def littleContourAreaForm (γ : ℝ≥0) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ →L[ℝ] ℝ :=
  (((ContinuousLinearMap.precompR (LittleContourSpace γ) (contourAreaForm γ)).flip
    (LittleContourSpace.inclusion γ)).comp (LittleContourSpace.inclusion γ))

theorem littleContourAreaForm_diagonal {γ : ℝ≥0} (f : LittleContourSpace γ) :
    littleContourAreaForm γ f f = loopArea (LittleContourSpace.lift γ f) :=
  contourAreaForm_diagonal f.val

def littleContourArea (γ : ℝ≥0) (f : LittleContourSpace γ) : ℝ :=
  loopArea (LittleContourSpace.lift γ f)

theorem analyticAt_littleContourArea {γ : ℝ≥0} (f : LittleContourSpace γ) :
    AnalyticAt ℝ (littleContourArea γ) f :=
  (analyticAt_contourArea f.val).comp ((LittleContourSpace.inclusion γ).analyticAt f)

theorem hasFDerivAt_littleContourArea_zero (γ : ℝ≥0) :
    HasFDerivAt (littleContourArea γ) (0 : LittleContourSpace γ →L[ℝ] ℝ) 0 := by
  have hd := (hasFDerivAt_contourArea_zero γ).comp (0 : LittleContourSpace γ)
    (LittleContourSpace.inclusion γ).hasFDerivAt
  unfold littleContourArea
  simpa only [ContinuousLinearMap.map_zero, ContinuousLinearMap.zero_comp,
    Function.comp_def, contourArea, LittleContourSpace.inclusion_apply,
    LittleContourSpace.lift] using hd

def littleContourEllCLM (γ : ℝ≥0) (r : ℝ) : LittleContourSpace γ →L[ℝ] ℝ :=
  (contourEllCLM γ r).comp (LittleContourSpace.inclusion γ)

theorem littleContourEllCLM_eq_ellFun {γ : ℝ≥0} (r : ℝ) (f : LittleContourSpace γ) :
    littleContourEllCLM γ r f = ellFun r (LittleContourSpace.lift γ f) :=
  contourEllCLM_eq_ellFun r f.val

/-- Real square root is actually analytic at every positive input. -/
theorem analyticAt_real_sqrt_pos {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have hs : AnalyticAt ℝ (fun t : ℝ => t ^ 2) (Real.sqrt x) := analyticAt_id.pow 2
  have hd : deriv (fun t : ℝ => t ^ 2) (Real.sqrt x) ≠ 0 := by
    rw [(hasDerivAt_pow 2 (Real.sqrt x)).deriv]
    simp only [Nat.cast_ofNat]
    positivity
  have hc : AnalyticAt ℝ (Real.sqrt ∘ (fun t : ℝ => t ^ 2)) (Real.sqrt x) := by
    apply (analyticAt_id : AnalyticAt ℝ (id : ℝ → ℝ) (Real.sqrt x)).congr
    filter_upwards [eventually_gt_nhds (Real.sqrt_pos.mpr hx)] with t ht
    simp only [Function.comp_apply, id_eq, Real.sqrt_sq ht.le]
  have ha := (analyticAt_comp_iff_of_deriv_ne_zero hs hd).mp hc
  simpa only [Real.sq_sqrt hx.le] using ha

end Euler2D

end
