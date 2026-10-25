module

public import RequestProject.Euler.ContourStarGeometry

/-! The actual Fréchet derivative and determinant of the radial-fan map,
with the parameter plane represented by the genuine complex plane. -/

@[expose] public section

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Euler2D

def contourFanMap (z : ℝ → ℂ) (p : ℂ) : ℂ := p.re • z p.im

def contourFanMapDerivative (z dz : ℝ → ℂ) (p : ℂ) : ℂ →L[ℝ] ℂ :=
  p.re • (Complex.imCLM.smulRight (dz p.im)) + Complex.reCLM.smulRight (z p.im)

theorem hasFDerivAt_contourFanMap {z dz : ℝ → ℂ}
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (p : ℂ) :
    HasFDerivAt (contourFanMap z) (contourFanMapDerivative z dz p) p := by
  have hzi : HasFDerivAt (fun q : ℂ => z q.im)
      (Complex.imCLM.smulRight (dz p.im)) p := by
    convert (hz p.im).hasFDerivAt.comp p Complex.imCLM.hasFDerivAt using 1
    · rfl
    · ext q
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
  exact Complex.reCLM.hasFDerivAt.smul hzi

theorem det_contourFanMapDerivative (z dz : ℝ → ℂ) (p : ℂ) :
    (contourFanMapDerivative z dz p).det =
      p.re * contourAngularJacobian z dz p.im := by
  change LinearMap.det (contourFanMapDerivative z dz p).toLinearMap = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [contourFanMapDerivative, LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, contourAngularJacobian, Complex.real_smul,
    Complex.mul_im, Complex.mul_re]
  ring

end Euler2D
