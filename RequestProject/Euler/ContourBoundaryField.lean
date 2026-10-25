module

public import RequestProject.Euler.ContourBoundaryInvariance

/-! The original finite-interface contour vector field, as an actual
logarithmic integral with actual derivatives. Its geometric invariances
are consequences of those integrals, rather than hypotheses on a field. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

def contourBoundaryField {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (z : ι → ℝ → ℂ) (i : ι) (θ : ℝ) : ℂ :=
  (-1 / (2 * Real.pi) : ℂ) * ∑ j, (g j : ℂ) *
    contourLogBoundaryIntegral (z j) (deriv (z j)) (z i θ)

theorem contourBoundaryField_rotShift {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (z : ι → ℝ → ℂ) (hz : ∀ j, Differentiable ℝ (z j))
    (hp : ∀ j, Function.Periodic (z j) (2 * Real.pi)) (b : ℝ) (i : ι) (θ : ℝ) :
    contourBoundaryField g (fun j => rotShift b (z j)) i θ =
      exp ((b : ℂ) * I) * contourBoundaryField g z i (θ - b) := by
  have hB (j : ι) : contourLogBoundaryIntegral (rotShift b (z j))
      (deriv (rotShift b (z j))) (rotShift b (z i) θ) =
      exp ((b : ℂ) * I) * contourLogBoundaryIntegral (z j) (deriv (z j)) (z i (θ - b)) :=
    contourLogBoundaryIntegral_rotShift (hz j) (hp j) b _
  unfold contourBoundaryField
  simp_rw [hB]
  calc
    _ = (-1 / (2 * Real.pi) : ℂ) * ∑ j, exp ((b : ℂ) * I) *
        ((g j : ℂ) * contourLogBoundaryIntegral (z j) (deriv (z j)) (z i (θ - b))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem contourBoundaryField_fourfold {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (z : ι → ℝ → ℂ) (hz : ∀ j, Differentiable ℝ (z j))
    (hp : ∀ j, Function.Periodic (z j) (2 * Real.pi))
    (hrot : ∀ j θ, z j (θ + Real.pi / 2) = I * z j θ) (i : ι) (θ : ℝ) :
    contourBoundaryField g z i (θ + Real.pi / 2) = I * contourBoundaryField g z i θ := by
  unfold contourBoundaryField
  rw [hrot]
  simp_rw [contourLogBoundaryIntegral_mul_I_of_fourfold (hz _) (hp _) (hrot _)]
  calc
    _ = (-1 / (2 * Real.pi) : ℂ) * ∑ j, I *
        ((g j : ℂ) * contourLogBoundaryIntegral (z j) (deriv (z j)) (z i θ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.mul_sum]; ring

def contourC1BoundaryField {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) : ι → ℝ → ℂ :=
  contourBoundaryField g (fun j => ContourC1Space.lift γ (Z j))

theorem contourC1BoundaryField_fourfold {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ)
    (hrot : ∀ j θ, ContourC1Space.lift γ (Z j) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z j) θ) (i : ι) (θ : ℝ) :
    contourC1BoundaryField g Z i (θ + Real.pi / 2) = I * contourC1BoundaryField g Z i θ :=
  contourBoundaryField_fourfold g _
    (fun j => (ContourC1Space.contDiff_lift (Z j)).differentiable one_ne_zero)
    (fun j => ContourC1Space.periodic_lift (Z j)) hrot i θ

end Euler2D
