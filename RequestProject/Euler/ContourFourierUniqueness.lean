module

public import RequestProject.Euler.ContourFourthModeProjection
public import Mathlib.Analysis.Fourier.AddCircle

/-! The actual contour Fourier coefficients agree with Mathlib's
normalized circle coefficients and separate the original little space. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

theorem fourier_contourCircle_coe (n : ℤ) (θ : ℝ) :
    fourier n (θ : ContourCircle) = contourCircleCharacter n θ := by
  rw [fourier_coe_apply, contourCircleCharacter]
  congr 1
  push_cast
  field_simp
  <;> ring

theorem littleContourFourierCoefficient_eq_fourierCoeff {γ : ℝ≥0}
    (k : ℤ) (H : LittleContourSpace γ) :
    littleContourFourierCoefficient γ k H =
      fourierCoeff (fun x => ContourC1Space.toBCF γ H.val x) k := by
  rw [littleContourFourierCoefficient, fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)]
  simp only [zero_add, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [fourier_contourCircle_coe]
  simp only [smul_eq_mul]
  exact mul_comm _ _

theorem littleContour_eq_zero_of_fourierCoefficient_eq_zero {γ : ℝ≥0}
    (H : LittleContourSpace γ) (hH : ∀ k : ℤ, littleContourFourierCoefficient γ k H = 0) :
    H = 0 := by
  let f : C(ContourCircle, ℂ) := (ContourC1Space.toBCF γ H.val).toContinuousMap
  have hf (k : ℤ) : fourierCoeff f k = 0 := by
    change fourierCoeff (fun x => ContourC1Space.toBCF γ H.val x) k = 0
    rw [← littleContourFourierCoefficient_eq_fourierCoeff k H]
    exact hH k
  have hs : Summable (fourierCoeff f) := by
    have he : fourierCoeff f = (fun _ : ℤ => (0 : ℂ)) := funext hf
    rw [he]
    exact summable_zero
  have hsum := hasSum_fourier_series_of_summable hs
  have hz : HasSum (fun _ : ℤ => (0 : C(ContourCircle, ℂ))) f := by
    simpa only [hf, zero_smul] using hsum
  have hfzero : f = 0 := hz.unique hasSum_zero
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  have he := congrArg (fun g : C(ContourCircle, ℂ) => g x) hfzero
  exact he

theorem littleContourFourierCoefficient_ext {γ : ℝ≥0}
    {H G : LittleContourSpace γ}
    (h : ∀ k : ℤ, littleContourFourierCoefficient γ k H = littleContourFourierCoefficient γ k G) :
    H = G := by
  apply sub_eq_zero.mp
  apply littleContour_eq_zero_of_fourierCoefficient_eq_zero
  intro k
  change littleContourFourierCoefficientCLM γ k (H - G) = 0
  rw [map_sub, littleContourFourierCoefficientCLM_apply, littleContourFourierCoefficientCLM_apply,
    h k, sub_self]

end Euler2D

end
