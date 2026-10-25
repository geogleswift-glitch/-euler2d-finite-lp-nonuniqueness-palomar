module

public import RequestProject.Euler.AreaChart
public import RequestProject.Euler.ContourHolderSpace

/-!
# Actual chord bounds and injectivity near a reference circle

The circular bound is derived from the complex exponential chord formula
and the sine inequality on a half-period.  The perturbation bound uses
the true derivative and the mean value theorem.  Short representatives
then identify the quotient-circle metric with the relevant angular gap.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real
open scoped ContDiff NNReal

namespace Euler2D

lemma norm_refCircle_sub (r θ φ : ℝ) (hr : 0 ≤ r) :
    ‖refCircle r θ - refCircle r φ‖ = 2 * r * |Real.sin ((θ - φ) / 2)| := by
  have hprod : Complex.exp ((φ : ℂ) * I) * Complex.exp (I * ((θ - φ : ℝ) : ℂ)) =
      Complex.exp ((θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he : Complex.exp ((θ : ℂ) * I) - Complex.exp ((φ : ℂ) * I) =
      Complex.exp ((φ : ℂ) * I) * (Complex.exp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, hprod]
  unfold refCircle
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

theorem refCircle_chord_lower {r θ φ : ℝ} (hr : 0 ≤ r) (hangle : |θ - φ| ≤ π) :
    (2 * r / π) * |θ - φ| ≤ ‖refCircle r θ - refCircle r φ‖ := by
  have hs := Real.mul_abs_le_abs_sin (x := (θ - φ) / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  calc
    _ = (2 * r) * ((2 / π) * |(θ - φ) / 2|) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (2 * r) * |Real.sin ((θ - φ) / 2)| := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := (norm_refCircle_sub r θ φ hr).symm

theorem norm_sub_le_of_contDiff_deriv_bound {p : ℝ → ℂ} {ε : ℝ}
    (hp : ContDiff ℝ 1 p) (hε : 0 ≤ ε) (hderiv : ∀ t, ‖deriv p t‖ ≤ ε) (θ φ : ℝ) :
    ‖p θ - p φ‖ ≤ ε * |θ - φ| := by
  have hnn (t : ℝ) : ‖deriv p t‖₊ ≤ NNReal.mk ε hε := by
    exact_mod_cast hderiv t
  have hLip := lipschitzWith_of_nnnorm_deriv_le (hp.differentiable one_ne_zero) hnn
  simpa only [NNReal.coe_mk, Real.norm_eq_abs] using hLip.norm_sub_le θ φ

theorem perturbed_refCircle_chord_lower {r ε θ φ : ℝ} {p : ℝ → ℂ}
    (hr : 0 ≤ r) (hp : ContDiff ℝ 1 p) (hε : 0 ≤ ε)
    (hderiv : ∀ t, ‖deriv p t‖ ≤ ε) (hangle : |θ - φ| ≤ π) :
    (2 * r / π - ε) * |θ - φ| ≤
      ‖(refCircle r θ + p θ) - (refCircle r φ + p φ)‖ := by
  have hc := refCircle_chord_lower hr hangle
  have hpbound := norm_sub_le_of_contDiff_deriv_bound hp hε hderiv θ φ
  have he : refCircle r θ - refCircle r φ =
      ((refCircle r θ + p θ) - (refCircle r φ + p φ)) - (p θ - p φ) := by abel
  have htri := norm_sub_le
    ((refCircle r θ + p θ) - (refCircle r φ + p φ)) (p θ - p φ)
  rw [← he] at htri
  nlinarith

theorem perturbed_refCircle_injective_of_short_gap {r ε θ φ : ℝ} {p : ℝ → ℂ}
    (hr : 0 ≤ r) (hp : ContDiff ℝ 1 p) (hε : 0 ≤ ε)
    (hderiv : ∀ t, ‖deriv p t‖ ≤ ε) (hsmall : ε < 2 * r / π)
    (hangle : |θ - φ| ≤ π)
    (heq : refCircle r θ + p θ = refCircle r φ + p φ) : θ = φ := by
  have hb := perturbed_refCircle_chord_lower hr hp hε hderiv hangle
  rw [heq, sub_self, norm_zero] at hb
  have hcoef : 0 < 2 * r / π - ε := sub_pos.mpr hsmall
  have hz : |θ - φ| ≤ 0 := (mul_le_mul_iff_right₀ hcoef).mp (by simpa only [mul_zero] using hb)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- The same true short-arc estimate, expressed directly for the actual real lift. -/
theorem contour_lift_chordArc_lower {r ε θ φ : ℝ} (z : ℝ → ℂ)
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hp : ContDiff ℝ 1 (fun t : ℝ => z t - refCircle r t))
    (hderiv : ∀ t : ℝ, ‖deriv (fun s : ℝ => z s - refCircle r s) t‖ ≤ ε)
    (hangle : |θ - φ| ≤ π) :
    (2 * r / π - ε) * |θ - φ| ≤ ‖z θ - z φ‖ := by
  have hb := perturbed_refCircle_chord_lower hr hp hε hderiv hangle
  have hz (t : ℝ) : refCircle r t + (z t - refCircle r t) = z t := by abel
  rwa [hz θ, hz φ] at hb

/-- Representatives realizing the true quotient-circle distance, with
their actual angular separation at most `π`. -/
theorem exists_short_contour_representatives (x y : ContourCircle) :
    ∃ θ φ : ℝ, (θ : ContourCircle) = x ∧ (φ : ContourCircle) = y ∧
      |θ - φ| ≤ π ∧ dist x y = |θ - φ| := by
  let δ : ℝ := (AddCircle.equivIco (2 * π) (-π) (x - y) : ℝ)
  let φ : ℝ := (AddCircle.equivIco (2 * π) 0 y : ℝ)
  let θ : ℝ := φ + δ
  have hδcoe : (δ : ContourCircle) = x - y :=
    (AddCircle.equivIco (2 * π) (-π)).symm_apply_apply (x - y)
  have hφcoe : (φ : ContourCircle) = y :=
    (AddCircle.equivIco (2 * π) 0).symm_apply_apply y
  have hθcoe : (θ : ContourCircle) = x := by
    dsimp only [θ]
    rw [AddCircle.coe_add, hφcoe, hδcoe]
    abel
  have hδlo : -π ≤ δ := (AddCircle.equivIco (2 * π) (-π) (x - y)).property.1
  have hδhi : δ < -π + 2 * π := (AddCircle.equivIco (2 * π) (-π) (x - y)).property.2
  have hδabs : |δ| ≤ π := abs_le.mpr ⟨hδlo, by linarith⟩
  have hsub : θ - φ = δ := by dsimp only [θ]; abel
  have hn : ‖(δ : ContourCircle)‖ = |δ| :=
    (AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).mpr (by
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith)
  refine ⟨θ, φ, hθcoe, hφcoe, ?_, ?_⟩
  · rw [hsub]
    exact hδabs
  · rw [dist_eq_norm, ← hδcoe, hn, hsub]

theorem contour_chordArc_lower {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (f : ContourCircle → ℂ)
    (hp : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle) - refCircle r θ))
    (hderiv : ∀ θ : ℝ, ‖deriv (fun t : ℝ => f (t : ContourCircle) - refCircle r t) θ‖ ≤ ε)
    (x y : ContourCircle) :
    (2 * r / π - ε) * dist x y ≤ ‖f x - f y‖ := by
  obtain ⟨θ, φ, hθ, hφ, hangle, hdist⟩ := exists_short_contour_representatives x y
  have hb := perturbed_refCircle_chord_lower hr hp hε hderiv hangle
  have hz (t : ℝ) : refCircle r t + (f (t : ContourCircle) - refCircle r t) =
      f (t : ContourCircle) := by abel
  rw [hz θ, hz φ, hθ, hφ] at hb
  rwa [hdist]

theorem continuous_of_contour_deviation_contDiff {r : ℝ} (f : ContourCircle → ℂ)
    (hp : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle) - refCircle r θ)) : Continuous f := by
  have hq : Topology.IsQuotientMap (fun θ : ℝ => (θ : ContourCircle)) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_iff.mpr
  have hcircle : Continuous (refCircle r) :=
    continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_refCircle r θ).continuousAt)
  exact (hcircle.add hp.continuous).congr (fun θ => by
    change refCircle r θ + (f (θ : ContourCircle) - refCircle r θ) = f (θ : ContourCircle)
    abel)

theorem injective_contour_of_deriv_deviation_small {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / π)
    (f : ContourCircle → ℂ)
    (hp : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle) - refCircle r θ))
    (hderiv : ∀ θ : ℝ, ‖deriv (fun t : ℝ => f (t : ContourCircle) - refCircle r t) θ‖ ≤ ε) :
    Function.Injective f := by
  intro x y hxy
  have hb := contour_chordArc_lower hr hε f hp hderiv x y
  rw [hxy, sub_self, norm_zero] at hb
  have hcoef : 0 < 2 * r / π - ε := sub_pos.mpr hsmall
  have hd : dist x y ≤ 0 := (mul_le_mul_iff_right₀ hcoef).mp (by simpa only [mul_zero] using hb)
  exact dist_le_zero.mp hd

theorem isClosedEmbedding_contour_of_deriv_deviation_small {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / π)
    (f : ContourCircle → ℂ)
    (hp : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle) - refCircle r θ))
    (hderiv : ∀ θ : ℝ, ‖deriv (fun t : ℝ => f (t : ContourCircle) - refCircle r t) θ‖ ≤ ε) :
    Topology.IsClosedEmbedding f :=
  (continuous_of_contour_deviation_contDiff f hp).isClosedEmbedding
    (injective_contour_of_deriv_deviation_small hr hε hsmall f hp hderiv)

end Euler2D

end
