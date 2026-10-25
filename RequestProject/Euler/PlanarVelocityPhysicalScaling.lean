module

public import RequestProject.Euler.ComplexDensityScaling

/-! The exact amplitude and length scaling of the actual planar
Biot--Savart integral, including its singular value convention. -/

@[expose] public section

noncomputable section

open Complex ComplexConjugate MeasureTheory

namespace Euler2D

theorem velocityC_scaledComplexDensity (A : ℝ) {r : ℝ} (hr : 0 < r)
    (w : ℂ → ℝ) (x : ℂ) :
    velocityC (scaledComplexDensity A r w) (r • x) =
      (A * r) • velocityC w x := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he (z : ℂ) :
      (scaledComplexDensity A r w z : ℂ) * ((r : ℂ) * x - z)⁻¹ =
        ((A : ℂ) * (r : ℂ)⁻¹) *
          ((w (r⁻¹ • z) : ℂ) * (x - r⁻¹ • z)⁻¹) := by
    have hz : (r : ℂ) * x - z = (r : ℂ) * (x - r⁻¹ • z) := by
      simp only [Complex.real_smul, Complex.ofReal_inv]
      field_simp
    rw [hz, mul_inv_rev]
    simp only [scaledComplexDensity, Complex.ofReal_mul]
    ring
  have hi :
      (∫ z : ℂ, (scaledComplexDensity A r w z : ℂ) * ((r : ℂ) * x - z)⁻¹) =
        ((A : ℂ) * (r : ℂ)) * ∫ z : ℂ, (w z : ℂ) * (x - z)⁻¹ := by
    rw [integral_congr_ae (ae_of_all _ he), integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg volume
        (fun z : ℂ => (w z : ℂ) * (x - z)⁻¹) hr.le,
      Complex.finrank_real_complex, Complex.real_smul, Complex.ofReal_pow]
    field_simp
  apply star_injective
  change conj (velocityC (scaledComplexDensity A r w) (r • x)) =
    conj ((A * r) • velocityC w x)
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal,
    conj_velocityC, hi, Complex.ofReal_mul]
  ring

end Euler2D

end
