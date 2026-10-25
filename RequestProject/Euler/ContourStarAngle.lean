module

public import RequestProject.Euler.ContourStarGeometry
public import RequestProject.Euler.ContourSmoothEmbedding

/-! A genuine increasing polar-angle parametrization of a small C¹
perturbation of a circle. The angle and its inverse are constructed from
the actual curve, rather than included as geometric assumptions. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology
open scoped ComplexConjugate NNReal

namespace Euler2D

theorem hasDerivAt_contourAngleLift {z : ℝ → ℂ} {r ε θ : ℝ} {dz : ℂ}
    (hr : 0 < r) (hsmall : ε < r)
    (hv : ‖z θ - refCircle r θ‖ ≤ ε) (hz : HasDerivAt z dz θ) :
    HasDerivAt (contourAngleLift z r) (dz / z θ).im θ := by
  have hv0 := refCircle_ne_zero_actual hr θ
  have hqslit := contourCircleRatio_mem_slitPlane hr hsmall hv
  have hq0 := Complex.slitPlane_ne_zero hqslit
  have hz0 : z θ ≠ 0 := by
    intro h
    exact hq0 (by simp [contourCircleRatio, h])
  have hq := hz.div (hasDerivAt_refCircle r θ) hv0
  have hlog := hq.clog_real hqslit
  have he : ((dz * refCircle r θ - z θ * (r * (I * exp ((θ : ℂ) * I)))) /
      (refCircle r θ) ^ 2) / contourCircleRatio z r θ = dz / z θ - I := by
    unfold contourCircleRatio refCircle
    dsimp only [refCircle] at hv0
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne', hz0]
    <;> ring
  have hl : HasDerivAt (fun s => Complex.log (contourCircleRatio z r s))
      (dz / z θ - I) θ := by
    convert hlog using 1
    exact he.symm
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hl
  have hi' : HasDerivAt (fun s => (Complex.log (contourCircleRatio z r s)).im)
      ((dz / z θ).im - 1) θ := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.sub_im, Complex.I_im] using hi
  convert (hasDerivAt_id θ).add hi' using 1 <;> simp [contourAngleLift]

theorem im_div_eq_angularJacobian {z dz : ℝ → ℂ} (θ : ℝ) :
    (dz θ / z θ).im = contourAngularJacobian z dz θ / ‖z θ‖ ^ 2 := by
  simp only [Complex.div_im, contourAngularJacobian, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_eq_norm_sq]
  ring

theorem strictMono_contourAngleLift {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) :
    StrictMono (contourAngleLift z r) := by
  have hs : ε < r := by linarith
  apply strictMono_of_hasDerivAt_pos
    (fun θ => hasDerivAt_contourAngleLift hr hs (hv θ) (hz θ))
  intro θ
  rw [im_div_eq_angularJacobian]
  exact div_pos (contourAngularJacobian_pos_of_quarter_radius hr hε hsmall (hv θ) (hd θ))
    (sq_pos_of_pos (norm_pos_iff.mpr (contour_ne_zero_of_quarter_radius hr hsmall (hv θ))))

theorem continuous_contourAngleLift {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hsmall : ε < r)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε) :
    Continuous (contourAngleLift z r) :=
  continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_contourAngleLift hr hsmall (hv θ) (hz θ)).continuousAt)

theorem tendsto_contourAngleLift_atTop (z : ℝ → ℂ) (r : ℝ) :
    Tendsto (contourAngleLift z r) atTop atTop := by
  apply tendsto_atTop_mono (f := fun θ : ℝ => θ + -Real.pi)
  · intro θ
    have h := (abs_le.mp (abs_contourAngleLift_sub_le_pi z r θ)).1
    linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_id

theorem tendsto_contourAngleLift_atBot (z : ℝ → ℂ) (r : ℝ) :
    Tendsto (contourAngleLift z r) atBot atBot := by
  apply tendsto_atBot_mono (g := fun θ : ℝ => θ + Real.pi)
  · intro θ
    have h := (abs_le.mp (abs_contourAngleLift_sub_le_pi z r θ)).2
    linarith
  · exact tendsto_atBot_add_const_right _ _ tendsto_id

theorem contourAngleLift_add_period {z : ℝ → ℂ}
    (hp : Function.Periodic z (2 * Real.pi)) (r θ : ℝ) :
    contourAngleLift z r (θ + 2 * Real.pi) = contourAngleLift z r θ + 2 * Real.pi := by
  simp only [contourAngleLift, contourCircleRatio, hp θ, periodic_refCircle r θ]
  ring

/-- The constructed angle is the actual direction of the curve. -/
theorem contour_polar_decomposition {z : ℝ → ℂ} {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    (‖z θ‖ : ℂ) * Complex.exp ((contourAngleLift z r θ : ℂ) * I) = z θ := by
  have hq : contourCircleRatio z r θ * refCircle r θ = z θ :=
    div_mul_cancel₀ _ (refCircle_ne_zero_actual hr θ)
  have hn : ‖z θ‖ = ‖contourCircleRatio z r θ‖ * r := by
    rw [← hq, norm_mul, norm_refCircle_actual, abs_of_pos hr]
  rw [contourAngleLift, Complex.log_im, Complex.ofReal_add, add_mul,
    Complex.exp_add, hn, Complex.ofReal_mul]
  calc
    _ = ((‖contourCircleRatio z r θ‖ : ℂ) *
        Complex.exp ((Complex.arg (contourCircleRatio z r θ) : ℂ) * I)) *
        refCircle r θ := by unfold refCircle; ring
    _ = contourCircleRatio z r θ * refCircle r θ := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = z θ := hq

/-- The polar angle is an actual order isomorphism of the real line. -/
def contourAngleOrderIso {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) : ℝ ≃o ℝ :=
  (strictMono_contourAngleLift hr hε hsmall hz hv hd).orderIsoOfSurjective _
    ((continuous_contourAngleLift hr (by linarith) hz hv).surjective
      (tendsto_contourAngleLift_atTop z r) (tendsto_contourAngleLift_atBot z r))

@[simp] theorem contourAngleOrderIso_apply {z dz : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ)
    (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
    (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε) (θ : ℝ) :
    contourAngleOrderIso hr hε hsmall hz hv hd θ = contourAngleLift z r θ := rfl

end Euler2D
