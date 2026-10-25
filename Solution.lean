module

public import RequestProject.Euler.FiniteLpNonuniqueness

/-! The proof of the independently stated Palomar declaration. This module
imports the substantive proof development and does not import Challenge. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open Euler2D

namespace PalomarEuler

/-- For every positive time horizon and every finite real spatial exponent
`p ≥ 1`, there are two unforced weak Euler solutions on the square torus
with the same mean-zero divergence-free `L² ∩ W¹ᵖ` initial datum, actual
strongly measurable Bochner `L∞ₜ Lp` vorticities, and positive space-time
`L²` distance. All definitions have their ordinary distributional meaning.
This is the two-dimensional finite-`Lp` question in Problem 6 of
Buckmaster and Vicol, Surveys in Mathematical Sciences 6 (2019), 173–263.
The separate comparison of critical regularity thresholds in that problem
is outside this statement. -/
theorem main_result (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 ≤ p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧
      MemW1p (ENNReal.ofReal p) u₀ ∧
      ∃ u₁ u₂ : ℝ → L2T, ∃ ω₁ ω₂ : ℝ → Lp ℝ (ENNReal.ofReal p) μT,
        IsWeakEulerSolution T u₀ u₁ ∧ IsWeakEulerSolution T u₀ u₂ ∧
        CurlBounded T (ENNReal.ofReal p) u₁ ∧ CurlBounded T (ENNReal.ofReal p) u₂ ∧
        StronglyMeasurable ω₁ ∧ StronglyMeasurable ω₂ ∧
        MemLp ω₁ ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp ω₂ ∞ (volume.restrict (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, IsCurl (u₁ t) (ω₁ t)) ∧
        (∀ t ∈ Icc 0 T, IsCurl (u₂ t) (ω₂ t)) ∧
        0 < spaceTimeDistSq T u₁ u₂ := by
  exact Euler2D.finiteLp_nonuniqueness T hT p hp

end PalomarEuler

end
