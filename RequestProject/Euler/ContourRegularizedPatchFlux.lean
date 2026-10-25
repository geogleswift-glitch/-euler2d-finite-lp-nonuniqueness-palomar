module

public import RequestProject.Euler.ContourAveragedStreamFlux
public import RequestProject.Euler.ContourRegularizedPatchBounds

/-! Zero flux of the genuine smooth regularizations of an actual patch,
derived from the actual regularized logarithmic potentials. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

theorem integral_normalFlux_regularizedPatch_zero
    {z dz : ℝ → ℂ} {Ω : Set ℂ} {R δ : ℝ}
    (hδ : δ ≠ 0) (hΩ : Ω ⊆ Metric.closedBall (0 : ℂ) R)
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdzc : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (-I * ∫ y in Ω, regularizedLogGradient (z θ) δ y) * dz θ).im) = 0 := by
  have ha := integral_normalFlux_averaged_stream_zero
    (ψ := fun y => regularizedLogPotential y δ)
    (dψ := fun y => regularizedLogPotentialDerivative y δ)
    (fun y => hasFDerivAt_regularizedLogPotential y hδ)
    (continuous_regularizedLogPotentialDerivative_pair hδ) hΩ hz hdzc hp
  simp_rw [complexRealGradient_regularizedLogPotentialDerivative] at ha
  have he (θ : ℝ) : (I * ∫ y in Ω, regularizedLogGradient y δ (z θ)) =
      -I * ∫ y in Ω, regularizedLogGradient (z θ) δ y := by
    have hf : (fun y => regularizedLogGradient y δ (z θ)) =
        fun y => -regularizedLogGradient (z θ) δ y :=
      funext (fun y => regularizedLogGradient_swap (z θ) y δ)
    rw [hf, integral_neg]
    ring
  simpa only [he] using ha

end Euler2D
