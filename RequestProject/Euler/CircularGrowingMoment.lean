module

public import RequestProject.Euler.CircularGrowingVariation
public import RequestProject.Euler.ContourBanachAreaChart
public import RequestProject.Euler.ContourC1GreenFormula
public import RequestProject.Euler.MomentVariation
public import RequestProject.Euler.ContourCircularRealModes

/-! The genuine fourth patch moment, expressed by Green's formula as a
continuous polynomial of the actual C¹ contour, and tested on the true
growing fourth Fourier direction. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ComplexConjugate BoundedContinuousFunction ContDiff

namespace Euler2D

local instance (priority := 2000) growingMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) growingMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

/-- Actual complex integration over the same parameter period used by the
Fourier coefficient calculations. -/
def contourComplexIntegralSymmetric : (ContourCircle →ᵇ ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ in (-Real.pi : ℝ)..Real.pi, f (θ : ContourCircle)
      map_add' := fun f g => by
        exact intervalIntegral.integral_add
          ((f.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _)
          ((g.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _)
      map_smul' := fun c f => intervalIntegral.integral_smul c _ }
    (2 * Real.pi) (fun f => by
      calc
        ‖∫ θ in (-Real.pi : ℝ)..Real.pi, f (θ : ContourCircle)‖ ≤
            ‖f‖ * |Real.pi - -Real.pi| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => f.norm_coe_le_norm _)
        _ = (2 * Real.pi) * ‖f‖ := by
          rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          ring)

def contourRealPartBCF : (ContourCircle →ᵇ ℂ) →L[ℝ] (ContourCircle →ᵇ ℂ) :=
  (Complex.ofRealCLM.comp Complex.reCLM).compLeftContinuousBounded ContourCircle

/-- The fourth domain moment written in genuine boundary coordinates.
Its equality with `momentJ` on the actual enclosed domain is proved below. -/
def contourFourthMoment (γ : ℝ≥0) (Z : ContourC1Space γ) : ℂ :=
  (-I / 5) * contourComplexIntegralSymmetric
    (contourRealPartBCF ((ContourC1Space.toBCF γ Z) ^ 5) * contourDerivativeBCF γ Z)

theorem contourFourthMoment_eq_integral {γ : ℝ≥0} (Z : ContourC1Space γ) :
    contourFourthMoment γ Z = (-I / 5) *
      ∫ θ in (-Real.pi : ℝ)..Real.pi,
        ((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) * deriv (ContourC1Space.lift γ Z) θ := by
  unfold contourFourthMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  change ((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) *
      ContourC1Space.derivative γ Z (θ : ContourCircle) = _
  rw [ContourC1Space.deriv_lift]

theorem contDiff_contourFourthMoment (γ : ℝ≥0) : ContDiff ℝ ∞ (contourFourthMoment γ) := by
  have hv := (ContourC1Space.toBCF γ).contDiff (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
  exact contDiff_const.mul (contourComplexIntegralSymmetric.contDiff.comp
    ((contourRealPartBCF.contDiff.comp (hv.pow 5)).mul (contourDerivativeBCF γ).contDiff))

def fourthMomentPotential (z : ℂ) : ℝ := (z ^ 5).re / 5

def fourthMomentPotentialDerivative (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (z ^ 4))

theorem hasFDerivAt_fourthMomentPotential (z : ℂ) :
    HasFDerivAt fourthMomentPotential (fourthMomentPotentialDerivative z) z := by
  have hp := ((hasDerivAt_id z).pow 5).hasFDerivAt.restrictScalars ℝ
  have hr := Complex.reCLM.hasFDerivAt.comp z hp
  have hd := hr.const_smul (1 / 5 : ℝ)
  convert hd using 1
  · funext w
    simp [fourthMomentPotential, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm]
  · ext w
    norm_num [fourthMomentPotentialDerivative, smul_eq_mul, Complex.mul_re,
      Complex.mul_im]
    ring

theorem complexRealGradient_fourthMomentPotential (z : ℂ) :
    complexRealGradient (fourthMomentPotentialDerivative z) = conj z ^ 4 := by
  apply Complex.ext <;>
    simp [complexRealGradient, fourthMomentPotentialDerivative,
      Complex.mul_re, Complex.mul_im, ← map_pow] <;> ring

theorem continuous_fourthMomentPotentialDerivative : Continuous fourthMomentPotentialDerivative := by
  exact continuous_const.clm_comp (continuous_const.clm_apply (continuous_id.pow 4))

theorem momentJ_contourC1EnclosedDomain_four {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    momentJ (contourC1EnclosedDomain Z Z₀ hr href hsmall) 4 = contourFourthMoment γ Z := by
  have hg := integral_gradient_contourC1EnclosedDomain Z Z₀ hr href hsmall
    hasFDerivAt_fourthMomentPotential continuous_fourthMomentPotentialDerivative
  simp only [complexRealGradient_fourthMomentPotential] at hg
  have hp : Function.Periodic
      (fun θ => ((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) *
        deriv (ContourC1Space.lift γ Z) θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_deriv_contour (ContourC1Space.periodic_lift Z)
      (ContourC1Space.contDiff_lift Z).differentiable_one θ, ContourC1Space.periodic_lift Z θ]
  have hperiod := hp.intervalIntegral_add_eq (0 : ℝ) (-Real.pi)
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [zero_add, hend] at hperiod
  rw [momentJ, hg, contourFourthMoment_eq_integral]
  simp only [fourthMomentPotential, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hpoint (θ : ℝ) :
      (((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) / 5) * deriv (ContourC1Space.lift γ Z) θ =
      (((ContourC1Space.lift γ Z θ ^ 5).re : ℂ) * deriv (ContourC1Space.lift γ Z) θ) / 5 := by ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_div, hperiod]
  ring

theorem hasDerivAt_contourFourthMoment {γ : ℝ≥0}
    {Z : ℝ → ContourC1Space γ} {H : ContourC1Space γ} {t : ℝ}
    (hZ : HasDerivAt Z H t) :
    HasDerivAt (fun s => contourFourthMoment γ (Z s))
      ((-I / 5) * ∫ θ in (-Real.pi : ℝ)..Real.pi,
        (5 : ℂ) * ((ContourC1Space.lift γ (Z t) θ ^ 4 *
          ContourC1Space.lift γ H θ).re : ℂ) * deriv (ContourC1Space.lift γ (Z t)) θ +
        ((ContourC1Space.lift γ (Z t) θ ^ 5).re : ℂ) * deriv (ContourC1Space.lift γ H) θ) t := by
  have hv := (ContourC1Space.toBCF γ).hasFDerivAt.comp_hasDerivAt t hZ
  have hp := hv.pow 5
  have hr := contourRealPartBCF.hasFDerivAt.comp_hasDerivAt t hp
  have hd := (contourDerivativeBCF γ).hasFDerivAt.comp_hasDerivAt t hZ
  have hm := contourComplexIntegralSymmetric.hasFDerivAt.comp_hasDerivAt t (hr.mul hd)
  have hf : HasDerivAt (fun s => contourFourthMoment γ (Z s)) _ t :=
    (hm.const_mul (-I / 5)).congr_of_eventuallyEq (Eventually.of_forall fun s => by
      simp only [contourFourthMoment, Function.comp_def, Pi.mul_apply, Pi.pow_apply])
  apply hf.congr_deriv
  apply congrArg (fun v : ℂ => (-I / 5) * v)
  change (∫ θ in (-Real.pi : ℝ)..Real.pi, _) = _
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only [Function.comp_def, Pi.pow_apply]
  rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
  change
    ((5 * ContourC1Space.lift γ (Z t) θ ^ (5 - 1) * ContourC1Space.lift γ H θ).re : ℂ) *
        ContourC1Space.derivative γ (Z t) (θ : ContourCircle) +
      ((ContourC1Space.lift γ (Z t) θ ^ 5).re : ℂ) *
        ContourC1Space.derivative γ H (θ : ContourCircle) = _
  norm_num [Complex.mul_re]
  push_cast
  ring
  all_goals simp

theorem circularFourthMomentBoundaryDerivative_twoModes (r : ℝ) (a b : ℂ) :
    (-I / 5) * (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (5 : ℂ) * ((((r : ℂ) * contourCircleCharacter 1 θ) ^ 4 *
        (a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ)).re : ℂ) *
          (I * r * contourCircleCharacter 1 θ) +
      ((((r : ℂ) * contourCircleCharacter 1 θ) ^ 5).re : ℂ) *
        (a * (5 * I * contourCircleCharacter 5 θ) +
          b * (-3 * I * contourCircleCharacter (-3) θ))) =
      Real.pi * (r : ℂ) ^ 5 * (a + conj b) := by
  let R (c : ℂ) (k l : ℤ) (θ : ℝ) : ℂ :=
    ((c * contourCircleCharacter k θ).re : ℂ) * contourCircleCharacter l θ
  have hR (c : ℂ) (k l : ℤ) : IntervalIntegrable (R c k l) volume (-Real.pi) Real.pi :=
    ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp
      (continuous_const.mul (continuous_contourCircleCharacter k)))).mul
      (continuous_contourCircleCharacter l)).intervalIntegrable _ _
  have hpoint (θ : ℝ) :
      (5 : ℂ) * ((((r : ℂ) * contourCircleCharacter 1 θ) ^ 4 *
        (a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ)).re : ℂ) *
          (I * r * contourCircleCharacter 1 θ) +
      ((((r : ℂ) * contourCircleCharacter 1 θ) ^ 5).re : ℂ) *
        (a * (5 * I * contourCircleCharacter 5 θ) +
          b * (-3 * I * contourCircleCharacter (-3) θ)) =
      (I * (r : ℂ) ^ 5) *
        (5 * (R a 9 1 θ + R b 1 1 θ) + 5 * a * R 1 5 5 θ - 3 * b * R 1 5 (-3) θ) := by
    have hprod : ((r : ℂ) * contourCircleCharacter 1 θ) ^ 4 *
        (a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ) =
        (r : ℂ) ^ 4 * (a * contourCircleCharacter 9 θ + b * contourCircleCharacter 1 θ) := by
      rw [mul_pow, contourCircleCharacter_pow]
      calc
        (r : ℂ) ^ 4 * contourCircleCharacter 4 θ *
            (a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ) =
            (r : ℂ) ^ 4 * (a * (contourCircleCharacter 4 θ * contourCircleCharacter 5 θ) +
              b * (contourCircleCharacter 4 θ * contourCircleCharacter (-3) θ)) := by ring
        _ = _ := by rw [contourCircleCharacter_mul, contourCircleCharacter_mul]; norm_num
    rw [hprod, mul_pow, contourCircleCharacter_pow]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re, R, one_mul, Complex.one_re, Complex.one_im,
      mul_one, add_zero]
    push_cast
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((((hR a 9 1).add (hR b 1 1)).const_mul 5).add ((hR 1 5 5).const_mul (5 * a)))
      ((hR 1 5 (-3)).const_mul (3 * b)),
    intervalIntegral.integral_add
      (((hR a 9 1).add (hR b 1 1)).const_mul 5) ((hR 1 5 5).const_mul (5 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hR a 9 1) (hR b 1 1)]
  simp only [R]
  rw [integral_contourCircular_realMode, integral_contourCircular_realMode,
    integral_contourCircular_realMode, integral_contourCircular_realMode]
  norm_num
  ring_nf
  simp only [I_sq]
  ring

theorem hasDerivAt_contourFourthMoment_fourthMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2)
    {Z : ℝ → ContourC1Space γ} {t : ℝ}
    (hZ : HasDerivAt Z (circularNormalModeC1 hγ hγ1 2 η τ i) t)
    (hZt : Z t = (littleReferenceCircle hγ hγ1 (circularContourRadii i)).val) :
    HasDerivAt (fun s => contourFourthMoment γ (Z s))
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) t := by
  let r := circularContourRadii i
  let a := circularNormalModePlus r (η i) (τ i)
  let b := circularNormalModeMinus r (η i) (τ i)
  have hzfun : ContourC1Space.lift γ (Z t) =
      fun θ => (r : ℂ) * contourCircleCharacter 1 θ := by
    rw [hZt]
    change LittleContourSpace.lift γ (littleReferenceCircle hγ hγ1 r) = _
    rw [lift_littleReferenceCircle]
    funext θ
    simp [refCircle, contourCircleCharacter]
  have hhfun : ContourC1Space.lift γ (circularNormalModeC1 hγ hγ1 2 η τ i) =
      fun θ => a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ := rfl
  have hzd (θ : ℝ) :
      deriv (fun θ => (r : ℂ) * contourCircleCharacter 1 θ) θ =
        I * r * contourCircleCharacter 1 θ := by
    rw [deriv_const_mul _ (hasDerivAt_contourCircleCharacter 1 θ).differentiableAt,
      deriv_contourCircleCharacter]
    norm_num
    ring
  have hhd (θ : ℝ) :
      deriv (fun θ => a * contourCircleCharacter 5 θ + b * contourCircleCharacter (-3) θ) θ =
        a * (5 * I * contourCircleCharacter 5 θ) + b * (-3 * I * contourCircleCharacter (-3) θ) := by
    convert (((hasDerivAt_contourCircleCharacter 5 θ).const_mul a).add
      ((hasDerivAt_contourCircleCharacter (-3) θ).const_mul b)).deriv using 1 <;> norm_num
  have hs : a + conj b = (r : ℂ) * η i := by
    simp only [a, b, circularNormalModePlus, circularNormalModeMinus,
      map_mul, map_add, map_div₀, map_ofNat, conj_ofReal, conj_I, conj_conj]
    ring
  have hd := hasDerivAt_contourFourthMoment hZ
  simp_rw [hzfun, hhfun, hzd, hhd] at hd
  rw [circularFourthMomentBoundaryDerivative_twoModes, hs] at hd
  convert hd using 1 <;> dsimp only [r] <;> ring

theorem hasDerivAt_littleAreaChart_fourthMoment {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    HasDerivAt (fun ε : ℝ => contourFourthMoment γ
      (littleAreaChart hγ hγ1 (circularContourRadii i)
        (ε • circularNormalModeLittle hγ hγ1 2 η τ i)).val)
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) 0 := by
  have hs : HasDerivAt (fun ε : ℝ => ε • circularNormalModeLittle hγ hγ1 2 η τ i)
      (circularNormalModeLittle hγ hγ1 2 η τ i) 0 := by
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularNormalModeLittle hγ hγ1 2 η τ i)
  have hchart : HasFDerivAt (littleAreaChart hγ hγ1 (circularContourRadii i))
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ))
      ((fun ε : ℝ => ε • circularNormalModeLittle hγ hγ1 2 η τ i) 0) := by
    simpa only [zero_smul] using hasFDerivAt_littleAreaChart_zero hγ hγ1 (circularContourRadii i)
  have hc := hchart.comp_hasDerivAt (0 : ℝ) hs
  have hc' := (LittleContourSpace.inclusion γ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  apply hasDerivAt_contourFourthMoment_fourthMode hγ hγ1 η τ i
  · simpa only [Function.comp_def, LittleContourSpace.inclusion_apply,
      circularNormalModeC1, ContinuousLinearMap.id_apply] using hc'
  · simp only [zero_smul, littleAreaChart_zero]

theorem circularGrowingMoment_boundary_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (i : Fin 2) :
    HasDerivAt (fun ε : ℝ => contourFourthMoment γ
      (littleAreaChart hγ hγ1.le (circularContourRadii i)
        (ε • circularGrowingVariation hγ hγ1 0 i)).val)
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * vPlus i) 0 := by
  rw [circularGrowingVariation_zero]
  exact hasDerivAt_littleAreaChart_fourthMoment hγ hγ1.le vPlus circularGrowingTangent i

theorem circularGrowingMoment_inner_derivative_ne_zero :
    Real.pi * (circularContourRadii 0 : ℂ) ^ 6 * vPlus 0 ≠ 0 := by
  simp only [circularContourRadii, vPlus, Matrix.cons_val_zero, mul_one]
  exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    (pow_ne_zero _ (ofReal_ne_zero.mpr cellA_pos.ne'))

/-- The genuine volume fourth moment of a nearby little contour. The
zero value outside the constructed near-circle neighborhood only makes
the function total; every result below is established inside that neighborhood. -/
def littlePatchFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r : ℝ) (hr : 0 < r) (Z : LittleContourSpace γ) : ℂ :=
  if hsmall : ‖Z.val - (littleReferenceCircle hγ hγ1 r).val‖ ≤ r / 4 then
    momentJ (contourC1EnclosedDomain Z.val (littleReferenceCircle hγ hγ1 r).val
      hr (lift_littleReferenceCircle hγ hγ1 r) hsmall) 4
  else 0

theorem littlePatchFourthMoment_eq_boundary {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) (Z : LittleContourSpace γ)
    (hsmall : ‖Z.val - (littleReferenceCircle hγ hγ1 r).val‖ ≤ r / 4) :
    littlePatchFourthMoment hγ hγ1 r hr Z = contourFourthMoment γ Z.val := by
  rw [littlePatchFourthMoment, dif_pos hsmall]
  exact momentJ_contourC1EnclosedDomain_four _ _ hr (lift_littleReferenceCircle hγ hγ1 r) hsmall

theorem littlePatchFourthMoment_eventually_eq_boundary {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) :
    littlePatchFourthMoment hγ hγ1 r hr =ᶠ[𝓝 (littleReferenceCircle hγ hγ1 r)]
      (fun Z => contourFourthMoment γ Z.val) := by
  have hn : ContinuousAt (fun Z : LittleContourSpace γ =>
      ‖Z.val - (littleReferenceCircle hγ hγ1 r).val‖) (littleReferenceCircle hγ hγ1 r) :=
    ((LittleContourSpace.inclusion γ).continuous.continuousAt.sub continuousAt_const).norm
  have hs : ∀ᶠ Z : LittleContourSpace γ in 𝓝 (littleReferenceCircle hγ hγ1 r),
      ‖Z.val - (littleReferenceCircle hγ hγ1 r).val‖ < r / 4 :=
    hn.eventually (eventually_lt_nhds (by simp only [sub_self, norm_zero]; positivity))
  filter_upwards [hs] with Z hZ
  exact littlePatchFourthMoment_eq_boundary hγ hγ1 hr Z hZ.le

theorem differentiableAt_littlePatchFourthMoment_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (littlePatchFourthMoment hγ hγ1 r hr) (littleReferenceCircle hγ hγ1 r) := by
  have hd : DifferentiableAt ℝ (fun Z : LittleContourSpace γ => contourFourthMoment γ Z.val)
      (littleReferenceCircle hγ hγ1 r) :=
    ((contDiff_contourFourthMoment γ).differentiable (by simp)).differentiableAt.comp _
      (LittleContourSpace.inclusion γ).differentiableAt
  exact hd.congr_of_eventuallyEq (littlePatchFourthMoment_eventually_eq_boundary hγ hγ1 hr)

theorem hasDerivAt_littlePatchFourthMoment_of_boundary {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : 0 < r)
    {Z : ℝ → LittleContourSpace γ} {t : ℝ} {v : ℂ}
    (hZc : ContinuousAt Z t) (hZt : Z t = littleReferenceCircle hγ hγ1 r)
    (hF : HasDerivAt (fun s => contourFourthMoment γ (Z s).val) v t) :
    HasDerivAt (fun s => littlePatchFourthMoment hγ hγ1 r hr (Z s)) v t := by
  have he := (littlePatchFourthMoment_eventually_eq_boundary hγ hγ1 hr).comp_tendsto
    (show Tendsto Z (𝓝 t) (𝓝 (littleReferenceCircle hγ hγ1 r)) from hZt ▸ hZc)
  exact hF.congr_of_eventuallyEq he

theorem growingMoment_radius_pos (i : Fin 2) : 0 < circularContourRadii i := by
  fin_cases i <;> simp [circularContourRadii, cellA_pos]

/-- The actual patch fourth moment in the original analytic area chart. -/
def circularAreaChartFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (i : Fin 2) (v : LittleContourSpace γ) : ℂ :=
  littlePatchFourthMoment hγ hγ1 (circularContourRadii i) (growingMoment_radius_pos i)
    (littleAreaChart hγ hγ1 (circularContourRadii i) v)

theorem differentiableAt_circularAreaChartFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (i : Fin 2) :
    DifferentiableAt ℝ (circularAreaChartFourthMoment hγ hγ1 i) 0 := by
  have hp : DifferentiableAt ℝ
      (littlePatchFourthMoment hγ hγ1 (circularContourRadii i) (growingMoment_radius_pos i))
      (littleAreaChart hγ hγ1 (circularContourRadii i) 0) := by
    simpa only [littleAreaChart_zero] using
      differentiableAt_littlePatchFourthMoment_reference hγ hγ1 (growingMoment_radius_pos i)
  exact hp.comp _ (hasFDerivAt_littleAreaChart_zero hγ hγ1 (circularContourRadii i)).differentiableAt

theorem circularGrowingMoment_patch_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (i : Fin 2) :
    HasDerivAt (fun ε : ℝ => circularAreaChartFourthMoment hγ hγ1.le i
      (ε • circularGrowingVariation hγ hγ1 0 i))
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * vPlus i) 0 := by
  have hs : HasDerivAt (fun ε : ℝ => ε • circularGrowingVariation hγ hγ1 0 i)
      (circularGrowingVariation hγ hγ1 0 i) 0 := by
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularGrowingVariation hγ hγ1 0 i)
  have hchart : HasFDerivAt (littleAreaChart hγ hγ1.le (circularContourRadii i))
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ))
      ((fun ε : ℝ => ε • circularGrowingVariation hγ hγ1 0 i) 0) := by
    simpa only [zero_smul] using hasFDerivAt_littleAreaChart_zero hγ hγ1.le (circularContourRadii i)
  apply hasDerivAt_littlePatchFourthMoment_of_boundary hγ hγ1.le (growingMoment_radius_pos i)
  · exact (hchart.comp_hasDerivAt (0 : ℝ) hs).continuousAt
  · simp only [zero_smul]
    exact littleAreaChart_zero hγ (by exact_mod_cast hγ1.le) (circularContourRadii i)
  · exact circularGrowingMoment_boundary_hasDerivAt hγ hγ1 i

theorem fderiv_circularAreaChartFourthMoment_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (i : Fin 2) :
    fderiv ℝ (circularAreaChartFourthMoment hγ hγ1.le i) 0
      (circularGrowingVariation hγ hγ1 0 i) =
      Real.pi * (circularContourRadii i : ℂ) ^ 6 * vPlus i := by
  have hs : HasDerivAt (fun ε : ℝ => ε • circularGrowingVariation hγ hγ1 0 i)
      (circularGrowingVariation hγ hγ1 0 i) 0 := by
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularGrowingVariation hγ hγ1 0 i)
  have hd : HasFDerivAt (circularAreaChartFourthMoment hγ hγ1.le i)
      (fderiv ℝ (circularAreaChartFourthMoment hγ hγ1.le i) 0)
      ((fun ε : ℝ => ε • circularGrowingVariation hγ hγ1 0 i) 0) := by
    simpa only [zero_smul] using
      (differentiableAt_circularAreaChartFourthMoment_zero hγ hγ1.le i).hasFDerivAt
  have hdc := hd.comp_hasDerivAt (0 : ℝ) hs
  change HasDerivAt (fun ε : ℝ => circularAreaChartFourthMoment hγ hγ1.le i
    (ε • circularGrowingVariation hγ hγ1 0 i))
    (fderiv ℝ (circularAreaChartFourthMoment hγ hγ1.le i) 0
      (circularGrowingVariation hγ hγ1 0 i)) 0 at hdc
  exact hdc.unique (circularGrowingMoment_patch_hasDerivAt hγ hγ1 i)

theorem fderiv_circularAreaChartFourthMoment_inner_growing_ne_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularAreaChartFourthMoment hγ hγ1.le 0) 0
      (circularGrowingVariation hγ hγ1 0 0) ≠ 0 := by
  rw [fderiv_circularAreaChartFourthMoment_growing]
  exact circularGrowingMoment_inner_derivative_ne_zero

theorem contourFourthMoment_reference_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    contourFourthMoment γ (littleReferenceCircle hγ hγ1 r).val = 0 := by
  have hzfun : ContourC1Space.lift γ (littleReferenceCircle hγ hγ1 r).val =
      fun θ => (r : ℂ) * contourCircleCharacter 1 θ := by
    change LittleContourSpace.lift γ (littleReferenceCircle hγ hγ1 r) = _
    rw [lift_littleReferenceCircle]
    funext θ
    simp [refCircle, contourCircleCharacter]
  have hzd (θ : ℝ) :
      deriv (fun θ => (r : ℂ) * contourCircleCharacter 1 θ) θ =
        I * r * contourCircleCharacter 1 θ := by
    rw [deriv_const_mul _ (hasDerivAt_contourCircleCharacter 1 θ).differentiableAt,
      deriv_contourCircleCharacter]
    norm_num
    ring
  rw [contourFourthMoment_eq_integral]
  simp_rw [hzfun, hzd]
  have hpoint (θ : ℝ) :
      ((((r : ℂ) * contourCircleCharacter 1 θ) ^ 5).re : ℂ) *
          (I * r * contourCircleCharacter 1 θ) =
      (I * (r : ℂ) ^ 6) * (((1 : ℂ) * contourCircleCharacter 5 θ).re : ℂ) *
        contourCircleCharacter 1 θ := by
    rw [mul_pow, contourCircleCharacter_pow]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, one_mul]
    push_cast
    ring
  simp_rw [hpoint, mul_assoc (I * (r : ℂ) ^ 6)]
  rw [intervalIntegral.integral_const_mul, integral_contourCircular_realMode]
  norm_num

theorem circularAreaChartFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (i : Fin 2) :
    circularAreaChartFourthMoment hγ hγ1 i 0 = 0 := by
  unfold circularAreaChartFourthMoment
  rw [littleAreaChart_zero, littlePatchFourthMoment_eq_boundary hγ hγ1
    (growingMoment_radius_pos i) _ (by
      simp only [sub_self, norm_zero]
      exact (div_pos (growingMoment_radius_pos i) (by norm_num : (0 : ℝ) < 4)).le)]
  exact contourFourthMoment_reference_zero hγ hγ1 (circularContourRadii i)

/-- The inner patch moment as an observable on the original family Banach space. -/
def circularFamilyInnerFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (v : Fin 2 → LittleContourSpace γ) : ℂ := circularAreaChartFourthMoment hγ hγ1 0 (v 0)

theorem differentiableAt_circularFamilyInnerFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    DifferentiableAt ℝ (circularFamilyInnerFourthMoment hγ hγ1) 0 := by
  let p : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ :=
    ContinuousLinearMap.proj 0
  have hg : DifferentiableAt ℝ (circularAreaChartFourthMoment hγ hγ1 0)
      (p (0 : Fin 2 → LittleContourSpace γ)) := by
    simpa only [ContinuousLinearMap.map_zero] using
      differentiableAt_circularAreaChartFourthMoment_zero hγ hγ1 0
  exact hg.comp (0 : Fin 2 → LittleContourSpace γ) p.differentiableAt

theorem circularFamilyInnerFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : circularFamilyInnerFourthMoment hγ hγ1 0 = 0 :=
  circularAreaChartFourthMoment_zero hγ hγ1 0

theorem fderiv_circularFamilyInnerFourthMoment_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularFamilyInnerFourthMoment hγ hγ1.le) 0
      (circularGrowingVariation hγ hγ1 0) = Real.pi * (cellA : ℂ) ^ 6 := by
  letI : IsBoundedSMul ℝ (Fin 2 → LittleContourSpace γ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Fin 2 → LittleContourSpace γ)
  letI : ContinuousSMul ℝ (Fin 2 → LittleContourSpace γ) := IsBoundedSMul.continuousSMul
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (circularFamilyInnerFourthMoment hγ hγle) 0
    (circularGrowingVariation hγ hγ1 0) = _
  let p : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ :=
    ContinuousLinearMap.proj 0
  have hd := (differentiableAt_circularAreaChartFourthMoment_zero hγ hγle 0).hasFDerivAt.comp
    (0 : Fin 2 → LittleContourSpace γ) p.hasFDerivAt
  have hfamily : HasFDerivAt (circularFamilyInnerFourthMoment hγ hγle)
      ((fderiv ℝ (circularAreaChartFourthMoment hγ hγle 0) 0).comp p) 0 := by
    change HasFDerivAt ((circularAreaChartFourthMoment hγ hγle 0) ∘ p)
      ((fderiv ℝ (circularAreaChartFourthMoment hγ hγle 0) 0).comp p) 0
    simpa only [ContinuousLinearMap.map_zero] using hd
  rw [hfamily.fderiv]
  change fderiv ℝ (circularAreaChartFourthMoment hγ hγle 0) 0
    (circularGrowingVariation hγ hγ1 0 0) = _
  have hi := fderiv_circularAreaChartFourthMoment_growing hγ hγ1 0
  change fderiv ℝ (circularAreaChartFourthMoment hγ hγle 0) 0
    (circularGrowingVariation hγ hγ1 0 0) =
      Real.pi * (circularContourRadii 0 : ℂ) ^ 6 * vPlus 0 at hi
  simpa only [circularContourRadii, vPlus, Matrix.cons_val_zero, mul_one] using hi

theorem fderiv_circularFamilyInnerFourthMoment_growing_ne_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularFamilyInnerFourthMoment hγ hγ1.le) 0
      (circularGrowingVariation hγ hγ1 0) ≠ 0 := by
  rw [fderiv_circularFamilyInnerFourthMoment_growing]
  exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    (pow_ne_zero _ (ofReal_ne_zero.mpr cellA_pos.ne'))

end Euler2D

end
