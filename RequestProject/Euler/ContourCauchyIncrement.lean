module

public import RequestProject.Euler.ContourC1Space
public import RequestProject.Euler.ContourChordArc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The genuinely integrable increment part of the contour Cauchy integral

The curve, its derivative and the density below are actual functions.  A
short-arc chord bound and a Hölder increment produce the integrable majorant
`|τ| ^ (γ - 1)`.  No principal-value identity is assumed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal Interval

namespace Euler2D

/-- The actual Cauchy integrand after subtracting the density at the base point. -/
def contourCauchyIncrementIntegrand (Z dZ f : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  (dZ (θ + τ) / (Z θ - Z (θ + τ))) * (f (θ + τ) - f θ)

@[simp] theorem contourCauchyIncrementIntegrand_zero (Z dZ f : ℝ → ℂ) (θ : ℝ) :
    contourCauchyIncrementIntegrand Z dZ f θ 0 = 0 := by
  simp [contourCauchyIncrementIntegrand]

/-- The actual weak power singularity is integrable across the origin. -/
theorem intervalIntegrable_abs_rpow_sub_one {γ a b : ℝ} (hγ : 0 < γ) :
    IntervalIntegrable (fun τ : ℝ => |τ| ^ (γ - 1)) volume a b := by
  apply intervalIntegrable_of_even (ha := by finiteness) (hb := by finiteness)
  · intro τ
    simp only [abs_neg]
  · intro r hr
    apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < γ - 1)
      (a := 0) (b := r)).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
    rw [uIoc_of_le hr.le] at hτ
    rw [abs_of_pos hτ.1]

/-- Explicit evaluation of the genuine symmetric power majorant. -/
theorem integral_abs_rpow_sub_one {γ r : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) :
    (∫ τ in Icc (-r) r, |τ| ^ (γ - 1)) = 2 * r ^ γ / γ := by
  have hi := intervalIntegrable_abs_rpow_sub_one (a := -r) (b := 0) hγ
  have hj := intervalIntegrable_abs_rpow_sub_one (a := 0) (b := r) hγ
  have hp : (∫ τ in (0 : ℝ)..r, |τ| ^ (γ - 1)) = r ^ γ / γ := by
    calc
      _ = ∫ τ in (0 : ℝ)..r, τ ^ (γ - 1) := by
        apply intervalIntegral.integral_congr
        intro τ hτ
        rw [uIcc_of_le hr] at hτ
        dsimp only
        rw [abs_of_nonneg hτ.1]
      _ = r ^ γ / γ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < γ - 1))]
        simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hγ), sub_zero]
  have hn : (∫ τ in (-r)..(0 : ℝ), |τ| ^ (γ - 1)) =
      ∫ τ in (0 : ℝ)..r, |τ| ^ (γ - 1) := by
    simpa only [neg_zero, neg_neg, abs_neg] using
      (intervalIntegral.integral_comp_neg (f := fun τ : ℝ => |τ| ^ (γ - 1))
        (a := -r) (b := 0))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    ← intervalIntegral.integral_add_adjacent_intervals hi hj, hn, hp]
  ring

theorem integrableOn_abs_rpow_sub_one {γ r : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) :
    IntegrableOn (fun τ : ℝ => |τ| ^ (γ - 1)) (Icc (-r) r) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -r ≤ r)).mp
    (intervalIntegrable_abs_rpow_sub_one hγ)

theorem measurable_contourCauchyIncrementIntegrand {Z dZ f : ℝ → ℂ}
    (hZ : Measurable Z) (hdZ : Measurable dZ) (hf : Measurable f) (θ : ℝ) :
    Measurable (contourCauchyIncrementIntegrand Z dZ f θ) :=
  (hdZ.comp (measurable_const.add measurable_id) |>.div
    (measurable_const.sub (hZ.comp (measurable_const.add measurable_id)))).mul
    ((hf.comp (measurable_const.add measurable_id)).sub measurable_const)

/-- The singularity is cancelled by the actual Hölder increment, including at zero. -/
theorem norm_contourCauchyIncrementIntegrand_le {Z dZ f : ℝ → ℂ}
    {θ τ γ c L H : ℝ} (hc : 0 < c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hchord : c * |τ| ≤ ‖Z θ - Z (θ + τ)‖)
    (hdZ : ‖dZ (θ + τ)‖ ≤ L)
    (hf : ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖contourCauchyIncrementIntegrand Z dZ f θ τ‖ ≤
      (L * H / c) * |τ| ^ (γ - 1) := by
  by_cases hτ : τ = 0
  · subst τ
    rw [contourCauchyIncrementIntegrand_zero, norm_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg hL hH) hc.le) (Real.rpow_nonneg (abs_nonneg _) _)
  have ht : 0 < |τ| := abs_pos.mpr hτ
  have hden : 0 < ‖Z θ - Z (θ + τ)‖ := (mul_pos hc ht).trans_le hchord
  calc
    _ = (‖dZ (θ + τ)‖ / ‖Z θ - Z (θ + τ)‖) * ‖f (θ + τ) - f θ‖ := by
      simp only [contourCauchyIncrementIntegrand, norm_mul, norm_div]
    _ ≤ (L / (c * |τ|)) * (H * |τ| ^ γ) := by
      apply mul_le_mul
      · exact div_le_div₀ hL hdZ (mul_pos hc ht) hchord
      · exact hf
      · exact norm_nonneg _
      · exact div_nonneg hL (mul_nonneg hc.le ht.le)
    _ = (L * H / c) * |τ| ^ (γ - 1) := by
      rw [Real.rpow_sub_one ht.ne']
      field_simp

/-- Raw-function integrability with the precise geometric and Hölder hypotheses. -/
theorem integrableOn_contourCauchyIncrementIntegrand {Z dZ f : ℝ → ℂ}
    {θ γ r c L H : ℝ} (hZ : Measurable Z) (hdZ : Measurable dZ) (hf : Measurable f)
    (hγ : 0 < γ) (hr : 0 ≤ r) (hc : 0 < c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hchord : ∀ τ ∈ Icc (-r) r, c * |τ| ≤ ‖Z θ - Z (θ + τ)‖)
    (hdZbound : ∀ τ ∈ Icc (-r) r, ‖dZ (θ + τ)‖ ≤ L)
    (hholder : ∀ τ ∈ Icc (-r) r, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    IntegrableOn (contourCauchyIncrementIntegrand Z dZ f θ) (Icc (-r) r) := by
  apply ((integrableOn_abs_rpow_sub_one hγ hr).const_mul (L * H / c)).mono'
    (measurable_contourCauchyIncrementIntegrand hZ hdZ hf θ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact norm_contourCauchyIncrementIntegrand_le hc hL hH
    (hchord τ hτ) (hdZbound τ hτ) (hholder τ hτ)

/-- Explicit L¹ bound for the actual increment integrand. -/
theorem integral_norm_contourCauchyIncrementIntegrand_le {Z dZ f : ℝ → ℂ}
    {θ γ r c L H : ℝ} (hZ : Measurable Z) (hdZ : Measurable dZ) (hf : Measurable f)
    (hγ : 0 < γ) (hr : 0 ≤ r) (hc : 0 < c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hchord : ∀ τ ∈ Icc (-r) r, c * |τ| ≤ ‖Z θ - Z (θ + τ)‖)
    (hdZbound : ∀ τ ∈ Icc (-r) r, ‖dZ (θ + τ)‖ ≤ L)
    (hholder : ∀ τ ∈ Icc (-r) r, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    (∫ τ in Icc (-r) r, ‖contourCauchyIncrementIntegrand Z dZ f θ τ‖) ≤
      (L * H / c) * (2 * r ^ γ / γ) := by
  have hi := integrableOn_contourCauchyIncrementIntegrand hZ hdZ hf hγ hr hc hL hH
    hchord hdZbound hholder
  calc
    _ ≤ ∫ τ in Icc (-r) r, (L * H / c) * |τ| ^ (γ - 1) := by
      apply integral_mono_ae hi.norm ((integrableOn_abs_rpow_sub_one hγ hr).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourCauchyIncrementIntegrand_le hc hL hH
        (hchord τ hτ) (hdZbound τ hτ) (hholder τ hτ)
    _ = _ := by rw [integral_const_mul, integral_abs_rpow_sub_one hγ hr]

/-- The actual Cauchy increment integral, with the literal relative parameter. -/
def contourCauchyIncrement (Z dZ f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ τ in Icc (-Real.pi) Real.pi, contourCauchyIncrementIntegrand Z dZ f θ τ

theorem norm_contourCauchyIncrement_le {Z dZ f : ℝ → ℂ}
    {θ γ c L H : ℝ} (hZ : Measurable Z) (hdZ : Measurable dZ) (hf : Measurable f)
    (hγ : 0 < γ) (hc : 0 < c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hchord : ∀ τ ∈ Icc (-Real.pi) Real.pi, c * |τ| ≤ ‖Z θ - Z (θ + τ)‖)
    (hdZbound : ∀ τ ∈ Icc (-Real.pi) Real.pi, ‖dZ (θ + τ)‖ ≤ L)
    (hholder : ∀ τ ∈ Icc (-Real.pi) Real.pi, ‖f (θ + τ) - f θ‖ ≤ H * |τ| ^ γ) :
    ‖contourCauchyIncrement Z dZ f θ‖ ≤ (L * H / c) * (2 * Real.pi ^ γ / γ) :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_contourCauchyIncrementIntegrand_le hZ hdZ hf hγ Real.pi_pos.le hc hL hH
      hchord hdZbound hholder)

/-- The genuine quotient-circle distance is dominated by the lifted increment. -/
theorem dist_contourCircle_add_le (θ τ : ℝ) :
    dist ((θ + τ : ℝ) : ContourCircle) (θ : ContourCircle) ≤ |τ| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * Real.pi))
      (m := (θ + τ) - θ))

/-- The actual Hölder norm controls the lifted increment, without choosing representatives. -/
theorem norm_contourHolder_lift_sub_le {γ : ℝ≥0} (f : ContourHolderSpace γ) (θ τ : ℝ) :
    ‖f ((θ + τ : ℝ) : ContourCircle) - f (θ : ContourCircle)‖ ≤
      ‖f‖ * |τ| ^ (γ : ℝ) :=
  (HolderFunctionSpace.norm_sub_le_holder f _ _).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_contourCircle_add_le θ τ) γ.coe_nonneg)
      (norm_nonneg f))

/-- Use the actual derivative of the contour in the complete C¹ Hölder space. -/
def contourC1CauchyIncrementIntegrand {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) (θ τ : ℝ) : ℂ :=
  contourCauchyIncrementIntegrand (ContourC1Space.lift γ Z)
    (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ τ

theorem measurable_contourC1_lift_deriv {γ : ℝ≥0} (Z : ContourC1Space γ) :
    Measurable (deriv (ContourC1Space.lift γ Z)) := by
  have heq : deriv (ContourC1Space.lift γ Z) =
      fun θ : ℝ => ContourC1Space.derivative γ Z (θ : ContourCircle) :=
    funext (ContourC1Space.deriv_lift Z)
  rw [heq]
  exact ((HolderFunctionSpace.toBCF γ (ContourC1Space.derivative γ Z)).continuous.comp
    (AddCircle.continuous_mk' (2 * Real.pi))).measurable

/-- The actual C¹/Hölder functions satisfy the raw integrability theorem. -/
theorem integrableOn_contourC1CauchyIncrementIntegrand {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) {θ c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ τ ∈ Icc (-Real.pi) Real.pi,
      c * |τ| ≤ ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    IntegrableOn (contourC1CauchyIncrementIntegrand Z f θ) (Icc (-Real.pi) Real.pi) := by
  apply integrableOn_contourCauchyIncrementIntegrand
    (ContourC1Space.contDiff_lift Z).continuous.measurable
    (measurable_contourC1_lift_deriv Z)
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ Real.pi_pos.le hc (norm_nonneg Z) (norm_nonneg f) hchord
  · intro τ _
    exact ContourC1Space.norm_deriv_lift_le Z (θ + τ)
  · intro τ _
    exact norm_contourHolder_lift_sub_le f θ τ

/-- The genuine increment integral on the C¹/Hölder contour spaces. -/
def contourC1CauchyIncrement {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) (θ : ℝ) : ℂ :=
  ∫ τ in Icc (-Real.pi) Real.pi, contourC1CauchyIncrementIntegrand Z f θ τ

/-- Explicit uniform bound in the actual contour and density norms. -/
theorem norm_contourC1CauchyIncrement_le {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) {θ c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ τ ∈ Icc (-Real.pi) Real.pi,
      c * |τ| ≤ ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ‖contourC1CauchyIncrement Z f θ‖ ≤
      (‖Z‖ * ‖f‖ / c) * (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) := by
  apply norm_contourCauchyIncrement_le
    (ContourC1Space.contDiff_lift Z).continuous.measurable
    (measurable_contourC1_lift_deriv Z)
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ hc (norm_nonneg Z) (norm_nonneg f) hchord
  · intro τ _
    exact ContourC1Space.norm_deriv_lift_le Z (θ + τ)
  · intro τ _
    exact norm_contourHolder_lift_sub_le f θ τ

/-- A genuine C¹ norm ball around a reference circle supplies the needed short-arc bound. -/
theorem contourC1_chord_lower_of_norm_sub {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 ≤ r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (θ : ℝ) {τ : ℝ} (hτ : τ ∈ Icc (-Real.pi) Real.pi) :
    (2 * r / Real.pi - ‖Z - Z₀‖) * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ := by
  have hp : ContDiff ℝ 1 (fun t : ℝ => ContourC1Space.lift γ Z t - refCircle r t) := by
    simpa only [ContourC1Space.lift_sub, Pi.sub_def, href] using
      (ContourC1Space.contDiff_lift (Z - Z₀))
  have hd : ∀ t : ℝ,
      ‖deriv (fun s : ℝ => ContourC1Space.lift γ Z s - refCircle r s) t‖ ≤ ‖Z - Z₀‖ := by
    intro t
    simpa only [ContourC1Space.lift_sub, Pi.sub_def, href] using
      (ContourC1Space.norm_deriv_lift_le (Z - Z₀) t)
  have hgap : |θ - (θ + τ)| = |τ| := by
    rw [show θ - (θ + τ) = -τ by ring, abs_neg]
  simpa only [hgap] using
    (contour_lift_chordArc_lower (ContourC1Space.lift γ Z) hr (norm_nonneg (Z - Z₀)) hp hd
      (θ := θ) (φ := θ + τ) (by simpa only [hgap] using abs_le.mpr hτ))

/-- Integrability now follows from a genuine norm neighborhood of an actual circle. -/
theorem integrableOn_contourC1CauchyIncrementIntegrand_near_circle {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hr : 0 ≤ r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    IntegrableOn (contourC1CauchyIncrementIntegrand Z f θ) (Icc (-Real.pi) Real.pi) :=
  integrableOn_contourC1CauchyIncrementIntegrand Z f hγ (sub_pos.mpr hsmall)
    (fun τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr href θ hτ)

/-- Explicit uniform integral bound throughout that genuine contour norm neighborhood. -/
theorem norm_contourC1CauchyIncrement_near_circle_le {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) (f : ContourHolderSpace γ) {r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hr : 0 ≤ r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    ‖contourC1CauchyIncrement Z f θ‖ ≤
      (‖Z‖ * ‖f‖ / (2 * r / Real.pi - ‖Z - Z₀‖)) *
        (2 * Real.pi ^ (γ : ℝ) / (γ : ℝ)) :=
  norm_contourC1CauchyIncrement_le Z f hγ (sub_pos.mpr hsmall)
    (fun τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr href θ hτ)

end Euler2D
