module

public import RequestProject.Euler.ContourReferenceCauchy
public import RequestProject.Euler.ContourC1Space

/-!
# Actual positive angular Jacobians near a circle

These estimates concern the actual values and derivatives of a loop.  In
particular, positivity is proved from its C¹ distance to a reference circle;
it is not an assumed geometric property of an enclosed domain.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped ComplexConjugate NNReal

namespace Euler2D

lemma norm_refCircle_actual (r θ : ℝ) : ‖refCircle r θ‖ = |r| := by
  simp [refCircle, Complex.norm_exp_ofReal_mul_I]

lemma refCircle_ne_zero_actual {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    refCircle r θ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_refCircle_actual, abs_of_pos hr]
  exact hr

lemma im_conj_refCircle_mul_deriv (r θ : ℝ) :
    (conj (refCircle r θ) * deriv (refCircle r) θ).im = r ^ 2 := by
  rw [deriv_refCircle_eq_I_mul]
  have he : conj (refCircle r θ) * (I * refCircle r θ) =
      I * (conj (refCircle r θ) * refCircle r θ) := by ring
  rw [he, Complex.conj_mul', norm_refCircle_actual]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    ← Complex.ofReal_pow, Complex.ofReal_re, sq_abs]

/-- The actual oriented area density, and the numerator of angular velocity. -/
def contourAngularJacobian (z dz : ℝ → ℂ) (θ : ℝ) : ℝ :=
  (conj (z θ) * dz θ).im

theorem norm_contour_sub_ref_bounds {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 ≤ r) (hz : ‖z θ - refCircle r θ‖ ≤ ε) :
    r - ε ≤ ‖z θ‖ ∧ ‖z θ‖ ≤ r + ε := by
  have h := norm_sub_norm_le (refCircle r θ) (z θ)
  rw [norm_sub_rev, norm_refCircle_actual, abs_of_nonneg hr] at h
  have hu := norm_add_le (z θ - refCircle r θ) (refCircle r θ)
  rw [sub_add_cancel] at hu
  rw [norm_refCircle_actual, abs_of_nonneg hr] at hu
  constructor <;> linarith

theorem abs_contourAngularJacobian_sub_circle {z dz : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hz : ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) :
    |contourAngularJacobian z dz θ - r ^ 2| ≤ 2 * r * ε + ε ^ 2 := by
  have hdz : ‖dz θ‖ ≤ r + ε := by
    have hh := norm_add_le (dz θ - deriv (refCircle r) θ) (deriv (refCircle r) θ)
    rw [sub_add_cancel] at hh
    rw [norm_deriv_refCircle hr] at hh
    linarith
  have he : conj (z θ) * dz θ - conj (refCircle r θ) * deriv (refCircle r) θ =
      conj (z θ - refCircle r θ) * dz θ +
        conj (refCircle r θ) * (dz θ - deriv (refCircle r) θ) := by
    simp only [map_sub]
    ring
  have hb : ‖conj (z θ) * dz θ -
      conj (refCircle r θ) * deriv (refCircle r) θ‖ ≤ 2 * r * ε + ε ^ 2 := by
    rw [he]
    calc
      _ ≤ ‖conj (z θ - refCircle r θ) * dz θ‖ +
          ‖conj (refCircle r θ) * (dz θ - deriv (refCircle r) θ)‖ := norm_add_le _ _
      _ = ‖z θ - refCircle r θ‖ * ‖dz θ‖ +
          r * ‖dz θ - deriv (refCircle r) θ‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj,
          norm_refCircle_actual, abs_of_nonneg hr]
      _ ≤ ε * (r + ε) + r * ε := add_le_add
        (mul_le_mul hz hdz (norm_nonneg _) hε)
        (mul_le_mul_of_nonneg_left hd hr)
      _ = _ := by ring
  have hi := (Complex.abs_im_le_norm
    (conj (z θ) * dz θ - conj (refCircle r θ) * deriv (refCircle r) θ)).trans hb
  simpa only [Complex.sub_im, im_conj_refCircle_mul_deriv, contourAngularJacobian] using hi

theorem contourAngularJacobian_lower {z dz : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hz : ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) :
    r ^ 2 - 2 * r * ε - ε ^ 2 ≤ contourAngularJacobian z dz θ := by
  have h := abs_contourAngularJacobian_sub_circle hr hε hz hd
  linarith [(abs_le.mp h).1]

theorem contourAngularJacobian_pos_of_quarter_radius {z dz : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) :
    0 < contourAngularJacobian z dz θ := by
  have hl := contourAngularJacobian_lower hr.le hε hz hd
  have hsq : ε ^ 2 ≤ (r / 4) ^ 2 := pow_le_pow_left₀ hε hsmall 2
  have hmul : 2 * r * ε ≤ 2 * r * (r / 4) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  nlinarith [sq_pos_of_pos hr]

theorem contour_ne_zero_of_quarter_radius {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hsmall : ε ≤ r / 4)
    (hz : ‖z θ - refCircle r θ‖ ≤ ε) : z θ ≠ 0 := by
  have hl := (norm_contour_sub_ref_bounds hr.le hz).1
  apply norm_pos_iff.mp
  linarith

/-- The actual quotient by the circular reference, rather than a selected
argument of the perturbed curve. -/
def contourCircleRatio (z : ℝ → ℂ) (r θ : ℝ) : ℂ := z θ / refCircle r θ

theorem norm_contourCircleRatio_sub_one {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hz : ‖z θ - refCircle r θ‖ ≤ ε) :
    ‖contourCircleRatio z r θ - 1‖ ≤ ε / r := by
  have he : contourCircleRatio z r θ - 1 =
      (z θ - refCircle r θ) / refCircle r θ := by
    unfold contourCircleRatio
    rw [sub_div, div_self (refCircle_ne_zero_actual hr θ)]
  rw [he, norm_div, norm_refCircle_actual, abs_of_pos hr]
  exact div_le_div_of_nonneg_right hz hr.le

theorem contourCircleRatio_mem_slitPlane {z : ℝ → ℂ} {r ε θ : ℝ}
    (hr : 0 < r) (hsmall : ε < r)
    (hz : ‖z θ - refCircle r θ‖ ≤ ε) :
    contourCircleRatio z r θ ∈ Complex.slitPlane := by
  have hb := (norm_contourCircleRatio_sub_one hr hz).trans_lt ((div_lt_one hr).mpr hsmall)
  simpa only [show 1 + (contourCircleRatio z r θ - 1) = contourCircleRatio z r θ by ring]
    using Complex.mem_slitPlane_of_norm_lt_one hb

/-- A single-valued actual angular lift, defined using a logarithm whose
slit-plane condition is proved by the preceding norm estimate. -/
def contourAngleLift (z : ℝ → ℂ) (r θ : ℝ) : ℝ :=
  θ + (Complex.log (contourCircleRatio z r θ)).im

theorem abs_contourAngleLift_sub_le_pi (z : ℝ → ℂ) (r θ : ℝ) :
    |contourAngleLift z r θ - θ| ≤ Real.pi := by
  simpa only [contourAngleLift, add_sub_cancel_left, Complex.log_im] using
    Complex.abs_arg_le_pi (contourCircleRatio z r θ)

section ActualC1

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
  (href : ContourC1Space.lift γ Z₀ = refCircle r)

include href

theorem contourC1_norm_sub_ref_le (θ : ℝ) :
    ‖ContourC1Space.lift γ Z θ - refCircle r θ‖ ≤ ‖Z - Z₀‖ := by
  rw [← href]
  exact ContourC1Space.norm_eval_le (Z - Z₀) (θ : ContourCircle)

theorem contourC1_norm_deriv_sub_ref_le (θ : ℝ) :
    ‖deriv (ContourC1Space.lift γ Z) θ - deriv (refCircle r) θ‖ ≤ ‖Z - Z₀‖ := by
  rw [← href, ← deriv_sub (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt
    (ContourC1Space.hasDerivAt_lift Z₀ θ).differentiableAt]
  exact ContourC1Space.norm_deriv_lift_le (Z - Z₀) θ

theorem contourC1AngularJacobian_pos (hr : 0 < r) (hsmall : ‖Z - Z₀‖ ≤ r / 4)
    (θ : ℝ) :
    0 < contourAngularJacobian (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) θ :=
  contourAngularJacobian_pos_of_quarter_radius (ε := ‖Z - Z₀‖) hr (norm_nonneg (Z - Z₀)) hsmall
    (contourC1_norm_sub_ref_le Z Z₀ href θ) (contourC1_norm_deriv_sub_ref_le Z Z₀ href θ)

theorem contourC1_ne_zero (hr : 0 < r) (hsmall : ‖Z - Z₀‖ ≤ r / 4)
    (θ : ℝ) : ContourC1Space.lift γ Z θ ≠ 0 :=
  contour_ne_zero_of_quarter_radius hr hsmall (contourC1_norm_sub_ref_le Z Z₀ href θ)

end ActualC1

end Euler2D
