module

public import RequestProject.Euler.ClusterField

/-! Exact physical scaling of the original complex volume density.
These are changes of variables in the actual plane integral. -/

@[expose] public section

noncomputable section

open Complex ComplexConjugate MeasureTheory

namespace Euler2D

def scaledComplexDensity (A r : ℝ) (w : ℂ → ℝ) (z : ℂ) : ℝ :=
  A * w (r⁻¹ • z)

theorem integrable_scaledComplexDensity {w : ℂ → ℝ} (hw : Integrable w)
    (A : ℝ) {r : ℝ} (hr : r ≠ 0) : Integrable (scaledComplexDensity A r w) :=
  (hw.comp_smul (inv_ne_zero hr)).const_mul A

theorem integral_scaledComplexDensity (A : ℝ) {r : ℝ} (hr : 0 ≤ r) (w : ℂ → ℝ) :
    (∫ z, scaledComplexDensity A r w z) = A * r ^ 2 * ∫ z, w z := by
  unfold scaledComplexDensity
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume w hr, Complex.finrank_real_complex,
    smul_eq_mul]
  ring

theorem momentN_scaledComplexDensity (A : ℝ) {r : ℝ} (hr : 0 < r)
    (w : ℂ → ℝ) (m : ℕ) :
    momentN (scaledComplexDensity A r w) m = (A : ℂ) * (r : ℂ) ^ (m + 2) * momentN w m := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he (z : ℂ) :
      (scaledComplexDensity A r w z : ℂ) * conj z ^ m =
        ((A : ℂ) * (r : ℂ) ^ m) * ((w (r⁻¹ • z) : ℂ) * conj (r⁻¹ • z) ^ m) := by
    simp only [scaledComplexDensity, ofReal_mul, Complex.real_smul, ofReal_inv, map_mul,
      map_inv₀, conj_ofReal, mul_pow, inv_pow]
    field_simp [hrC]
  rw [momentN, integral_congr_ae (ae_of_all _ he), integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z : ℂ => (w z : ℂ) * conj z ^ m) hr.le,
    Complex.finrank_real_complex, Complex.real_smul, ofReal_pow]
  simp only [momentN, pow_add]
  ring

theorem absMoment_scaledComplexDensity (A : ℝ) {r : ℝ} (hr : 0 < r)
    (w : ℂ → ℝ) (m : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ m * |scaledComplexDensity A r w z|) =
      |A| * r ^ (m + 2) * ∫ z : ℂ, ‖z‖ ^ m * |w z| := by
  have he (z : ℂ) :
      ‖z‖ ^ m * |scaledComplexDensity A r w z| =
        (|A| * r ^ m) * (‖r⁻¹ • z‖ ^ m * |w (r⁻¹ • z)|) := by
    simp only [scaledComplexDensity, abs_mul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, mul_pow, inv_pow]
    field_simp
  rw [integral_congr_ae (ae_of_all _ he), integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z : ℂ => ‖z‖ ^ m * |w z|) hr.le,
    Complex.finrank_real_complex, smul_eq_mul]
  rw [pow_add]
  ring

theorem scaledComplexDensity_support {w : ℂ → ℝ} {S r : ℝ}
    (hsupp : ∀ z, S < ‖z‖ → w z = 0) (hr : 0 < r) (A : ℝ) :
    ∀ z, r * S < ‖z‖ → scaledComplexDensity A r w z = 0 := by
  intro z hz
  rw [scaledComplexDensity, hsupp, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  exact (lt_inv_mul_iff₀ hr).mpr hz

theorem scaledComplexDensity_fourfold {w : ℂ → ℝ}
    (hsym : ∀ z, w (I * z) = w z) (A r : ℝ) (z : ℂ) :
    scaledComplexDensity A r w (I * z) = scaledComplexDensity A r w z := by
  simp only [scaledComplexDensity, Complex.real_smul]
  rw [show ((r⁻¹ : ℝ) : ℂ) * (I * z) = I * (((r⁻¹ : ℝ) : ℂ) * z) by ring, hsym]

end Euler2D

end
