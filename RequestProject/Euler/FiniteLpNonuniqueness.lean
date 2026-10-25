module

public import RequestProject.Euler.Theorems
public import RequestProject.Euler.BochnerVorticity

/-!
# Nonuniqueness at every finite spatial exponent, including one

The original main theorem is applied at `q = max p 2`. Finite-measure
exponent inclusion gives the requested Sobolev and curl bounds at `p`.
The vorticities are genuine strongly measurable, essentially bounded
curves with values in spatial `Lp`, and satisfy the original curl identity
at every time. No measurability, existence, or compactness assumption is
supplied by the caller.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Euler2D

/-- The two-dimensional finite-`Lp` nonuniqueness statement: arbitrary positive
time interval, arbitrary real `p ≥ 1`, a common mean-zero divergence-free
`L² ∩ W¹ᵖ` initial datum, and two distinct unforced weak Euler solutions
with actual Bochner `L∞`-in-time `Lp` vorticities. -/
theorem finiteLp_nonuniqueness (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 ≤ p) :
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
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  let q : ℝ := max p 2
  have hpq : p ≤ q := le_max_left _ _
  have hq : 2 ≤ q := le_max_right _ _
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hpq
  have hp1E : (1 : ENNReal) ≤ ENNReal.ofReal p := Fact.out
  obtain ⟨u₀, hmean, hdiv, hW, u₁, u₂, hu₁, hu₂, hc₁, hc₂, hdist⟩ :=
    main_nonuniqueness T hT q hq1
  obtain ⟨ω₁, hω₁sm, hω₁mem, hω₁curl⟩ :=
    exists_bochner_vorticity_of_weakEuler_lowerExponent hp hpq hq hu₁ hc₁
  obtain ⟨ω₂, hω₂sm, hω₂mem, hω₂curl⟩ :=
    exists_bochner_vorticity_of_weakEuler_lowerExponent hp hpq hq hu₂ hc₂
  exact ⟨u₀, hmean, hdiv, hW.mono_exponent hpqE, u₁, u₂, ω₁, ω₂, hu₁, hu₂,
    curlBounded_mono_exponent hp1E ENNReal.ofReal_ne_top hpqE hc₁,
    curlBounded_mono_exponent hp1E ENNReal.ofReal_ne_top hpqE hc₂,
    hω₁sm, hω₂sm, hω₁mem, hω₂mem, hω₁curl, hω₂curl, hdist⟩

end Euler2D
