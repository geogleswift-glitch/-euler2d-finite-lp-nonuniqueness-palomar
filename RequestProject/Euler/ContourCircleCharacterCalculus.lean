module

public import RequestProject.Euler.ContourCircularRadialBounds
public import RequestProject.Euler.ContourSmoothEmbedding

/-! Actual integer Fourier modes and their genuine smooth embeddings
in the original little contour Banach space. -/

@[expose] public section

noncomputable section

open Complex
open scoped NNReal ContDiff

namespace Euler2D

@[simp] theorem contourCircleCharacter_at_zero (k : ℤ) : contourCircleCharacter k 0 = 1 := by
  simp [contourCircleCharacter]

theorem contourCircleCharacter_add_arg (k : ℤ) (θ φ : ℝ) :
    contourCircleCharacter k (θ + φ) = contourCircleCharacter k θ * contourCircleCharacter k φ := by
  simp only [contourCircleCharacter, Complex.ofReal_add, mul_add, add_mul, exp_add]

theorem inv_contourCircleCharacter (k : ℤ) (θ : ℝ) :
    (contourCircleCharacter k θ)⁻¹ = contourCircleCharacter (-k) θ := by
  rw [contourCircleCharacter, ← exp_neg, contourCircleCharacter]
  congr 1
  push_cast
  ring

theorem contDiff_contourCircleCharacter (k : ℤ) : ContDiff ℝ ∞ (contourCircleCharacter k) := by
  unfold contourCircleCharacter
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp

theorem hasDerivAt_contourCircleCharacter (k : ℤ) (θ : ℝ) :
    HasDerivAt (contourCircleCharacter k) ((k : ℂ) * I * contourCircleCharacter k θ) θ := by
  unfold contourCircleCharacter
  have hd := ((((hasDerivAt_id θ).ofReal_comp).const_mul (k : ℂ)).mul_const I).cexp
  convert hd using 1 <;> simp only [id_eq, Complex.ofReal_one, mul_one] <;> ring

theorem deriv_contourCircleCharacter (k : ℤ) (θ : ℝ) :
    deriv (contourCircleCharacter k) θ = (k : ℂ) * I * contourCircleCharacter k θ :=
  (hasDerivAt_contourCircleCharacter k θ).deriv

def littleContourFourierMode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℤ) (a : ℂ) :
    LittleContourSpace γ :=
  littleContourOfPeriodicSmooth hγ hγ1 (fun θ => a * contourCircleCharacter k θ)
    (fun θ => congrArg (a * ·) (periodic_contourCircleCharacter k θ))
    (contDiff_const.mul (contDiff_contourCircleCharacter k))

@[simp] theorem lift_littleContourFourierMode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℤ) (a : ℂ) (θ : ℝ) :
    LittleContourSpace.lift γ (littleContourFourierMode hγ hγ1 k a) θ = a * contourCircleCharacter k θ := rfl

theorem deriv_lift_littleContourFourierMode {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℤ) (a : ℂ) (θ : ℝ) :
    deriv (LittleContourSpace.lift γ (littleContourFourierMode hγ hγ1 k a)) θ =
      a * ((k : ℂ) * I * contourCircleCharacter k θ) :=
  ((hasDerivAt_contourCircleCharacter k θ).const_mul a).deriv

end Euler2D

end
