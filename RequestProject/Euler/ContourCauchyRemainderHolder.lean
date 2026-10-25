module

public import RequestProject.Euler.ContourCauchyPrincipalValue

/-!
# Actual Hölder estimates for the contour Cauchy remainder

The kernel estimates are proved from the true curve derivative, its
Hölder modulus, and the genuine chord lower bound.  The pole remainder
is then integrated against the genuine density increment.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

/-- The true curve chords vary Hölder continuously in their base point, with a factor `|τ|`. -/
theorem norm_contour_chord_parameter_sub_le {z dz : ℝ → ℂ} {γ H : ℝ}
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ) (θ η τ : ℝ) :
    ‖(z θ - z (θ + τ)) - (z η - z (η + τ))‖ ≤
      (H * |θ - η| ^ γ) * |τ| := by
  let g : ℝ → ℂ := fun s => z (θ + s) - z (η + s)
  have hg (s : ℝ) : HasDerivAt g (dz (θ + s) - dz (η + s)) s := by
    simpa only [g, Pi.sub_def, Function.comp_def, one_smul] using
      ((hz (θ + s)).scomp s ((hasDerivAt_id s).const_add θ)).sub
        ((hz (η + s)).scomp s ((hasDerivAt_id s).const_add η))
  have hb (s : ℝ) (_hs : s ∈ uIcc (0 : ℝ) τ) :
      ‖dz (θ + s) - dz (η + s)‖ ≤ H * |θ - η| ^ γ := by
    simpa only [add_sub_add_right_eq_sub] using hd (θ + s) (η + s)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_hs : s ∈ uIcc (0 : ℝ) τ) => (hg s).hasDerivWithinAt)
    hb (convex_uIcc (0 : ℝ) τ) left_mem_uIcc right_mem_uIcc
  have heq : g τ - g 0 = -((z θ - z (θ + τ)) - (z η - z (η + τ))) := by
    dsimp only [g, add_zero]
    abel_nf
  rw [heq, norm_neg] at hm
  simpa only [sub_zero, Real.norm_eq_abs] using hm

/-- Actual kernel variation: Hölder variation of both numerator and chord is retained. -/
theorem norm_contourCauchyPoleIntegrand_parameter_sub_le {z dz : ℝ → ℂ}
    {γ H L c θ η τ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hc : 0 < c)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hdL : ∀ s, ‖dz s‖ ≤ L)
    (hθ : c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hη : c * |τ| ≤ ‖z η - z (η + τ)‖) :
    ‖contourCauchyPoleIntegrand z dz θ τ - contourCauchyPoleIntegrand z dz η τ‖ ≤
      (H / c + L * H / c ^ 2) * |θ - η| ^ γ / |τ| := by
  by_cases hτ : τ = 0
  · subst τ
    simp [contourCauchyPoleIntegrand]
  have ht : 0 < |τ| := abs_pos.mpr hτ
  let A := z θ - z (θ + τ)
  let B := z η - z (η + τ)
  have hA : 0 < ‖A‖ := (mul_pos hc ht).trans_le hθ
  have hB : 0 < ‖B‖ := (mul_pos hc ht).trans_le hη
  have hAn : A ≠ 0 := norm_pos_iff.mp hA
  have hBn : B ≠ 0 := norm_pos_iff.mp hB
  have hP : c * |τ| * (c * |τ|) ≤ ‖A‖ * ‖B‖ :=
    mul_le_mul hθ hη (mul_nonneg hc.le ht.le) (norm_nonneg A)
  have hBA : ‖B - A‖ ≤ (H * |θ - η| ^ γ) * |τ| := by
    rw [norm_sub_rev]
    exact norm_contour_chord_parameter_sub_le hz hd θ η τ
  have hnum : ‖dz (η + τ)‖ * ‖B - A‖ ≤ L * ((H * |θ - η| ^ γ) * |τ|) :=
    mul_le_mul (hdL _) hBA (norm_nonneg _) hL
  have hsplit : dz (θ + τ) / A - dz (η + τ) / B =
      (dz (θ + τ) - dz (η + τ)) / A + dz (η + τ) * (B - A) / (A * B) := by
    field_simp
    ring
  have hdnum : ‖dz (θ + τ) - dz (η + τ)‖ ≤ H * |θ - η| ^ γ := by
    simpa only [add_sub_add_right_eq_sub] using hd (θ + τ) (η + τ)
  simp only [contourCauchyPoleIntegrand, add_sub_add_right_eq_sub]
  change ‖dz (θ + τ) / A - dz (η + τ) / B‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖(dz (θ + τ) - dz (η + τ)) / A‖ + ‖dz (η + τ) * (B - A) / (A * B)‖ :=
      norm_add_le _ _
    _ = ‖dz (θ + τ) - dz (η + τ)‖ / ‖A‖ +
        (‖dz (η + τ)‖ * ‖B - A‖) / (‖A‖ * ‖B‖) := by simp only [norm_div, norm_mul]
    _ ≤ (H * |θ - η| ^ γ) / (c * |τ|) +
        (L * ((H * |θ - η| ^ γ) * |τ|)) / (c * |τ| * (c * |τ|)) := by
      apply add_le_add
      · exact div_le_div₀ (mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) _)) hdnum
          (mul_pos hc ht) hθ
      · exact div_le_div₀ (mul_nonneg hL (mul_nonneg (mul_nonneg hH
          (Real.rpow_nonneg (abs_nonneg _) _)) ht.le)) hnum
          (mul_pos (mul_pos hc ht) (mul_pos hc ht)) hP
    _ = _ := by
      field_simp

/-- The actual remainder paired with the actual density increment. -/
def contourCauchyResidualIncrementIntegrand (z dz f : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  contourCauchyPoleIntegrand z dz θ τ * (f (θ + τ) - f θ)

def contourCauchyResidualIncrement (z dz f : ℝ → ℂ) (r θ : ℝ) : ℂ :=
  ∫ τ in Icc (-r) r, contourCauchyResidualIncrementIntegrand z dz f θ τ

def contourRemainderUniformConstant (γ H c r : ℝ) : ℝ :=
  (2 * H / c) * r ^ γ * (2 * r ^ γ / γ)

def contourRemainderHolderConstant (γ H L c r : ℝ) : ℝ :=
  (2 * (2 * H / c) + (H / c + L * H / c ^ 2)) * (2 * r ^ γ / γ)

theorem contourRemainderUniformConstant_nonneg {γ H c r : ℝ}
    (hγ : 0 < γ) (hH : 0 ≤ H) (hc : 0 < c) (hr : 0 ≤ r) :
    0 ≤ contourRemainderUniformConstant γ H c r := by
  unfold contourRemainderUniformConstant
  positivity

theorem contourRemainderHolderConstant_nonneg {γ H L c r : ℝ}
    (hγ : 0 < γ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hc : 0 < c) (hr : 0 ≤ r) :
    0 ≤ contourRemainderHolderConstant γ H L c r := by
  unfold contourRemainderHolderConstant
  positivity

theorem integrableOn_contourCauchyResidualIncrementIntegrand
    {z dz f : ℝ → ℂ} {γ H c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hfc : Continuous f)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hc : 0 < c) (hr : 0 ≤ r)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    IntegrableOn (contourCauchyResidualIncrementIntegrand z dz f θ) (Icc (-r) r) :=
  (integrableOn_contourCauchyPoleIntegrand hzc hdzc hγ hH hc hr hz hd hchord θ).mul_continuousOn
    ((hfc.comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn isCompact_Icc

/-- Explicit uniform bound for the actual remainder-increment integral. -/
theorem norm_contourCauchyResidualIncrement_le {z dz f : ℝ → ℂ} {γ H Hf c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hfc : Continuous f)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hHf : 0 ≤ Hf) (hc : 0 < c) (hr : 0 ≤ r)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hf : ∀ s t, ‖f s - f t‖ ≤ Hf * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    ‖contourCauchyResidualIncrement z dz f r θ‖ ≤
      contourRemainderUniformConstant γ H c r * Hf := by
  have hA : 0 ≤ 2 * H / c := by positivity
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-r) r) :
      ‖contourCauchyResidualIncrementIntegrand z dz f θ τ‖ ≤
        ((2 * H / c) * (Hf * r ^ γ)) * |τ| ^ (γ - 1) := by
    have hfτ : ‖f (θ + τ) - f θ‖ ≤ Hf * r ^ γ := by
      have hs := hf (θ + τ) θ
      simp only [add_sub_cancel_left] at hs
      exact hs.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (abs_le.mpr hτ) hγ.le) hHf)
    have hR := norm_contourCauchyPoleIntegrand_le hγ.le hH hc hz hd
      (hchord θ τ (abs_le.mpr hτ))
    calc
      _ = ‖contourCauchyPoleIntegrand z dz θ τ‖ * ‖f (θ + τ) - f θ‖ := norm_mul _ _
      _ ≤ ((2 * H / c) * |τ| ^ (γ - 1)) * (Hf * r ^ γ) :=
        mul_le_mul hR hfτ (norm_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (abs_nonneg _) _))
      _ = _ := by ring
  have hm := (integrableOn_abs_rpow_sub_one hγ hr).const_mul ((2 * H / c) * (Hf * r ^ γ))
  calc
    _ ≤ ∫ τ in Icc (-r) r, ((2 * H / c) * (Hf * r ^ γ)) * |τ| ^ (γ - 1) := by
      apply norm_integral_le_of_norm_le hm
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact hb τ hτ
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_sub_one hγ hr]
      unfold contourRemainderUniformConstant
      ring

/-- Pointwise cancellation leaves a genuinely integrable Hölder difference majorant. -/
theorem norm_contourCauchyResidualIncrementIntegrand_sub_le
    {z dz f : ℝ → ℂ} {γ H L Hf c θ η τ : ℝ}
    (hγ : 0 ≤ γ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hHf : 0 ≤ Hf) (hc : 0 < c)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ)
    (hdL : ∀ s, ‖dz s‖ ≤ L)
    (hf : ∀ s t, ‖f s - f t‖ ≤ Hf * |s - t| ^ γ)
    (hθ : c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hη : c * |τ| ≤ ‖z η - z (η + τ)‖) :
    ‖contourCauchyResidualIncrementIntegrand z dz f θ τ -
        contourCauchyResidualIncrementIntegrand z dz f η τ‖ ≤
      ((2 * (2 * H / c) + (H / c + L * H / c ^ 2)) * Hf * |θ - η| ^ γ) *
        |τ| ^ (γ - 1) := by
  have hA : 0 ≤ 2 * H / c := by positivity
  have hD : 0 ≤ H / c + L * H / c ^ 2 := by positivity
  by_cases hτ : τ = 0
  · subst τ
    simp only [contourCauchyResidualIncrementIntegrand, contourCauchyPoleIntegrand, add_zero,
      sub_self, div_zero, Complex.ofReal_zero, inv_zero, zero_mul, norm_zero]
    positivity
  have ht : 0 < |τ| := abs_pos.mpr hτ
  have hinc : ‖(f (θ + τ) - f θ) - (f (η + τ) - f η)‖ ≤
      2 * Hf * |θ - η| ^ γ := by
    have hsplit : (f (θ + τ) - f θ) - (f (η + τ) - f η) =
        (f (θ + τ) - f (η + τ)) - (f θ - f η) := by abel
    rw [hsplit]
    calc
      _ ≤ ‖f (θ + τ) - f (η + τ)‖ + ‖f θ - f η‖ := norm_sub_le _ _
      _ ≤ Hf * |θ - η| ^ γ + Hf * |θ - η| ^ γ := by
        apply add_le_add
        · simpa only [add_sub_add_right_eq_sub] using hf (θ + τ) (η + τ)
        · exact hf θ η
      _ = _ := by ring
  have hfη : ‖f (η + τ) - f η‖ ≤ Hf * |τ| ^ γ := by
    simpa only [add_sub_cancel_left] using hf (η + τ) η
  have hR := norm_contourCauchyPoleIntegrand_le hγ hH hc hz hd hθ
  have hDR := norm_contourCauchyPoleIntegrand_parameter_sub_le hH hL hc hz hd hdL hθ hη
  have heq : contourCauchyResidualIncrementIntegrand z dz f θ τ -
      contourCauchyResidualIncrementIntegrand z dz f η τ =
      contourCauchyPoleIntegrand z dz θ τ * ((f (θ + τ) - f θ) - (f (η + τ) - f η)) +
      (contourCauchyPoleIntegrand z dz θ τ - contourCauchyPoleIntegrand z dz η τ) *
        (f (η + τ) - f η) := by
    dsimp only [contourCauchyResidualIncrementIntegrand]
    ring
  rw [heq]
  calc
    _ ≤ ‖contourCauchyPoleIntegrand z dz θ τ‖ * ‖(f (θ + τ) - f θ) - (f (η + τ) - f η)‖ +
        ‖contourCauchyPoleIntegrand z dz θ τ - contourCauchyPoleIntegrand z dz η τ‖ *
          ‖f (η + τ) - f η‖ := by
      simpa only [norm_mul] using norm_add_le
        (contourCauchyPoleIntegrand z dz θ τ * ((f (θ + τ) - f θ) - (f (η + τ) - f η)))
        ((contourCauchyPoleIntegrand z dz θ τ - contourCauchyPoleIntegrand z dz η τ) *
          (f (η + τ) - f η))
    _ ≤ ((2 * H / c) * |τ| ^ (γ - 1)) * (2 * Hf * |θ - η| ^ γ) +
        ((H / c + L * H / c ^ 2) * |θ - η| ^ γ / |τ|) * (Hf * |τ| ^ γ) := by
      apply add_le_add
      · exact mul_le_mul hR hinc (norm_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (abs_nonneg _) _))
      · exact mul_le_mul hDR hfη (norm_nonneg _) (div_nonneg
          (mul_nonneg hD (Real.rpow_nonneg (abs_nonneg _) _)) ht.le)
    _ = _ := by
      rw [Real.rpow_sub_one ht.ne']
      ring

/-- A quantitative genuine Hölder bound for the actual remainder increment operator. -/
theorem norm_contourCauchyResidualIncrement_sub_le {z dz f : ℝ → ℂ} {γ H L Hf c r : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hfc : Continuous f)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hHf : 0 ≤ Hf) (hc : 0 < c) (hr : 0 ≤ r)
    (hz : ∀ s, HasDerivAt z (dz s) s)
    (hd : ∀ s t, ‖dz s - dz t‖ ≤ H * |s - t| ^ γ) (hdL : ∀ s, ‖dz s‖ ≤ L)
    (hf : ∀ s t, ‖f s - f t‖ ≤ Hf * |s - t| ^ γ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ η : ℝ) :
    ‖contourCauchyResidualIncrement z dz f r θ - contourCauchyResidualIncrement z dz f r η‖ ≤
      (contourRemainderHolderConstant γ H L c r * Hf) * |θ - η| ^ γ := by
  have hiθ := integrableOn_contourCauchyResidualIncrementIntegrand hzc hdzc hfc hγ hH hc hr hz hd hchord θ
  have hiη := integrableOn_contourCauchyResidualIncrementIntegrand hzc hdzc hfc hγ hH hc hr hz hd hchord η
  unfold contourCauchyResidualIncrement
  rw [← integral_sub hiθ hiη]
  calc
    _ ≤ ∫ τ in Icc (-r) r,
        ((2 * (2 * H / c) + (H / c + L * H / c ^ 2)) * Hf * |θ - η| ^ γ) * |τ| ^ (γ - 1) := by
      apply norm_integral_le_of_norm_le ((integrableOn_abs_rpow_sub_one hγ hr).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_contourCauchyResidualIncrementIntegrand_sub_le hγ.le hH hL hHf hc hz hd hdL hf
        (hchord θ τ (abs_le.mpr hτ)) (hchord η τ (abs_le.mpr hτ))
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_sub_one hγ hr]
      unfold contourRemainderHolderConstant
      ring

theorem periodic_contourCauchyResidualIncrement {z dz f : ℝ → ℂ} {p : ℝ} (r : ℝ)
    (hz : Function.Periodic z p) (hdz : Function.Periodic dz p) (hf : Function.Periodic f p) :
    Function.Periodic (contourCauchyResidualIncrement z dz f r) p := by
  intro θ
  unfold contourCauchyResidualIncrement
  apply integral_congr_ae
  filter_upwards [] with τ
  have hadd : (θ + p) + τ = (θ + τ) + p := by ring
  simp only [contourCauchyResidualIncrementIntegrand, contourCauchyPoleIntegrand, hadd,
    hz (θ + τ), hdz (θ + τ), hf (θ + τ), hz θ, hf θ]

theorem norm_contourHolder_lift_sub_global_le {γ : ℝ≥0} (f : ContourHolderSpace γ) (s t : ℝ) :
    ‖f (s : ContourCircle) - f (t : ContourCircle)‖ ≤ ‖f‖ * |s - t| ^ (γ : ℝ) := by
  have h := norm_contourHolder_lift_sub_le f t (s - t)
  have heq : t + (s - t) = s := by ring
  rwa [heq] at h

private lemma continuous_contourHolder_lift {γ : ℝ≥0} (f : ContourHolderSpace γ) :
    Continuous (fun t : ℝ => f (t : ContourCircle)) :=
  (HolderFunctionSpace.toBCF γ f).continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))

private lemma continuous_contourC1_deriv {γ : ℝ≥0} (Z : ContourC1Space γ) :
    Continuous (deriv (ContourC1Space.lift γ Z)) :=
  (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2

def contourC1CauchyResidualIncrement {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) : ℝ → ℂ :=
  contourCauchyResidualIncrement (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z))
    (fun t : ℝ => f (t : ContourCircle)) Real.pi

theorem periodic_contourC1CauchyResidualIncrement {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) :
    Function.Periodic (contourC1CauchyResidualIncrement Z f) (2 * Real.pi) := by
  apply periodic_contourCauchyResidualIncrement
  · exact ContourC1Space.periodic_lift Z
  · intro θ
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
    exact congrArg (ContourC1Space.derivative γ Z) (AddCircle.coe_add_period (2 * Real.pi) θ)
  · intro θ
    exact congrArg f (AddCircle.coe_add_period (2 * Real.pi) θ)

/-- The actual residue increment, descended to the genuine quotient circle. -/
def contourCauchyResidualOnCircle {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) : ContourCircle → ℂ :=
  (periodic_contourC1CauchyResidualIncrement Z f).lift

@[simp] theorem contourCauchyResidualOnCircle_coe {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyResidualOnCircle Z f (θ : ContourCircle) = contourC1CauchyResidualIncrement Z f θ := rfl

theorem norm_contourC1CauchyResidualIncrement_le {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    ‖contourC1CauchyResidualIncrement Z f θ‖ ≤
      contourRemainderUniformConstant (γ : ℝ) ‖Z‖ c Real.pi * ‖f‖ :=
  norm_contourCauchyResidualIncrement_le (ContourC1Space.contDiff_lift Z).continuous
    (continuous_contourC1_deriv Z) (continuous_contourHolder_lift f) hγ (norm_nonneg Z)
    (norm_nonneg f) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) (norm_contourHolder_lift_sub_global_le f) hchord θ

theorem norm_contourC1CauchyResidualIncrement_sub_le {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ η : ℝ) :
    ‖contourC1CauchyResidualIncrement Z f θ - contourC1CauchyResidualIncrement Z f η‖ ≤
      (contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi * ‖f‖) * |θ - η| ^ (γ : ℝ) :=
  norm_contourCauchyResidualIncrement_sub_le (ContourC1Space.contDiff_lift Z).continuous
    (continuous_contourC1_deriv Z) (continuous_contourHolder_lift f) hγ (norm_nonneg Z)
    (norm_nonneg Z) (norm_nonneg f) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) (ContourC1Space.norm_deriv_lift_le Z)
    (norm_contourHolder_lift_sub_global_le f) hchord θ η

/-- The actual quotient-circle remainder is Hölder, with a quantitative constant. -/
theorem holderWith_contourCauchyResidualOnCircle {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    HolderWith (⟨contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi * ‖f‖,
      mul_nonneg (contourRemainderHolderConstant_nonneg hγ (norm_nonneg Z) (norm_nonneg Z)
        hc Real.pi_pos.le) (norm_nonneg f)⟩ : ℝ≥0) γ (contourCauchyResidualOnCircle Z f) := by
  change HolderWith
    (NNReal.mk (contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi * ‖f‖)
      (mul_nonneg (contourRemainderHolderConstant_nonneg hγ (norm_nonneg Z) (norm_nonneg Z)
        hc Real.pi_pos.le) (norm_nonneg f))) γ (contourCauchyResidualOnCircle Z f)
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (contourCauchyResidualOnCircle Z f x) (contourCauchyResidualOnCircle Z f y) ≤
      (contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi * ‖f‖) * dist x y ^ (γ : ℝ) := by
    obtain ⟨θ, η, hθ, hη, _, hdist⟩ := exists_short_contour_representatives x y
    have h := norm_contourC1CauchyResidualIncrement_sub_le Z f hγ hc hchord θ η
    rw [← contourCauchyResidualOnCircle_coe, ← contourCauchyResidualOnCircle_coe,
      hθ, hη, ← hdist] at h
    simpa only [dist_eq_norm] using h
  exact_mod_cast hb

/-- Actual closedness in the genuine complete Hölder space. -/
def contourCauchyResidualHolder {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (f : ContourHolderSpace γ) : ContourHolderSpace γ :=
  contourHolderOfMemHolder (by exact_mod_cast hγ) (contourCauchyResidualOnCircle Z f)
    (holderWith_contourCauchyResidualOnCircle Z f hγ hc hchord).memHolder

@[simp] theorem contourCauchyResidualHolder_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourCauchyResidualHolder Z hγ hc hchord f x = contourCauchyResidualOnCircle Z f x := rfl

theorem norm_contourCauchyResidualHolder_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (f : ContourHolderSpace γ) :
    ‖contourCauchyResidualHolder Z hγ hc hchord f‖ ≤
      (contourRemainderUniformConstant (γ : ℝ) ‖Z‖ c Real.pi +
        contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi) * ‖f‖ := by
  have hU := contourRemainderUniformConstant_nonneg hγ (norm_nonneg Z) hc Real.pi_pos.le
  have hC := contourRemainderHolderConstant_nonneg hγ (norm_nonneg Z) (norm_nonneg Z) hc Real.pi_pos.le
  rw [HolderFunctionSpace.norm_eq_max_uniform_holder]
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg (add_nonneg hU hC) (norm_nonneg f))).mpr
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖contourC1CauchyResidualIncrement Z f θ‖ ≤ _
    exact (norm_contourC1CauchyResidualIncrement_le Z f hγ hc hchord θ).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (norm_nonneg f))
  · have hh := (holderWith_contourCauchyResidualOnCircle Z f hγ hc hchord).nnholderNorm_le
    have hn : (nnHolderNorm γ (contourCauchyResidualOnCircle Z f) : ℝ) ≤
        contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi * ‖f‖ := by exact_mod_cast hh
    exact hn.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hU) (norm_nonneg f))

theorem contourCauchyResidualIncrement_add {z dz f g : ℝ → ℂ} {r θ : ℝ}
    (hf : IntegrableOn (contourCauchyResidualIncrementIntegrand z dz f θ) (Icc (-r) r))
    (hg : IntegrableOn (contourCauchyResidualIncrementIntegrand z dz g θ) (Icc (-r) r)) :
    contourCauchyResidualIncrement z dz (f + g) r θ =
      contourCauchyResidualIncrement z dz f r θ + contourCauchyResidualIncrement z dz g r θ := by
  have heq : contourCauchyResidualIncrementIntegrand z dz (f + g) θ =
      fun τ => contourCauchyResidualIncrementIntegrand z dz f θ τ +
        contourCauchyResidualIncrementIntegrand z dz g θ τ := by
    ext τ
    dsimp only [contourCauchyResidualIncrementIntegrand, Pi.add_apply]
    ring
  unfold contourCauchyResidualIncrement
  rw [heq, integral_add hf hg]

theorem contourCauchyResidualIncrement_smul (z dz f : ℝ → ℂ) (r θ a : ℝ) :
    contourCauchyResidualIncrement z dz (a • f) r θ =
      a • contourCauchyResidualIncrement z dz f r θ := by
  have heq : contourCauchyResidualIncrementIntegrand z dz (a • f) θ =
      fun τ => a • contourCauchyResidualIncrementIntegrand z dz f θ τ := by
    ext τ
    dsimp only [contourCauchyResidualIncrementIntegrand, Pi.smul_apply]
    simp only [Complex.real_smul]
    ring
  unfold contourCauchyResidualIncrement
  rw [heq, integral_smul]

theorem integrableOn_contourC1CauchyResidualIncrementIntegrand {γ : ℝ≥0}
    (Z : ContourC1Space γ) (f : ContourHolderSpace γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    IntegrableOn (contourCauchyResidualIncrementIntegrand (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ)
      (Icc (-Real.pi) Real.pi) :=
  integrableOn_contourCauchyResidualIncrementIntegrand (ContourC1Space.contDiff_lift Z).continuous
    (continuous_contourC1_deriv Z) (continuous_contourHolder_lift f) hγ (norm_nonneg Z) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord θ

/-- The genuine remainder integral as a linear map on the actual Hölder space. -/
def contourCauchyResidualLinearMap {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ContourHolderSpace γ →ₗ[ℝ] ContourHolderSpace γ where
  toFun := contourCauchyResidualHolder Z hγ hc hchord
  map_add' f g := by
    apply HolderFunctionSpace.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change contourCauchyResidualIncrement (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z))
        ((fun t : ℝ => f (t : ContourCircle)) + (fun t : ℝ => g (t : ContourCircle))) Real.pi θ = _
    exact contourCauchyResidualIncrement_add
      (integrableOn_contourC1CauchyResidualIncrementIntegrand Z f hγ hc hchord θ)
      (integrableOn_contourC1CauchyResidualIncrementIntegrand Z g hγ hc hchord θ)
  map_smul' a f := by
    apply HolderFunctionSpace.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change contourCauchyResidualIncrement (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (a • (fun t : ℝ => f (t : ContourCircle))) Real.pi θ = _
    exact contourCauchyResidualIncrement_smul _ _ _ _ _ _

/-- A truly bounded remainder operator on the complete contour Hölder space. -/
def contourCauchyResidualOperator {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  (contourCauchyResidualLinearMap Z hγ hc hchord).mkContinuous
    (contourRemainderUniformConstant (γ : ℝ) ‖Z‖ c Real.pi +
      contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi)
    (norm_contourCauchyResidualHolder_le Z hγ hc hchord)

@[simp] theorem contourCauchyResidualOperator_apply {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (f : ContourHolderSpace γ) (θ : ℝ) :
    contourCauchyResidualOperator Z hγ hc hchord f (θ : ContourCircle) =
      contourC1CauchyResidualIncrement Z f θ := rfl

theorem norm_contourCauchyResidualOperator_le {γ : ℝ≥0} (Z : ContourC1Space γ) {c : ℝ}
    (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) :
    ‖contourCauchyResidualOperator Z hγ hc hchord‖ ≤
      contourRemainderUniformConstant (γ : ℝ) ‖Z‖ c Real.pi +
        contourRemainderHolderConstant (γ : ℝ) ‖Z‖ ‖Z‖ c Real.pi := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact add_nonneg (contourRemainderUniformConstant_nonneg hγ (norm_nonneg Z) hc Real.pi_pos.le)
      (contourRemainderHolderConstant_nonneg hγ (norm_nonneg Z) (norm_nonneg Z) hc Real.pi_pos.le)
  · exact norm_contourCauchyResidualHolder_le Z hγ hc hchord

end Euler2D
