module

public import Mathlib

/-!
# Conservation for transported labels (Lemma `cs:lem:conservation`)

Write `ω(t) = ω(0) ∘ X_t⁻¹`. The paper's proof uses two facts about the particle flow `X_t`:
it preserves Lebesgue measure, and it commutes with the quarter turn `x ↦ ix` (from uniqueness
and rotational covariance). Here these two facts are hypotheses on a measurable equivalence
`X : ℂ ≃ᵐ ℂ`, and we prove the conclusions: the integral, the `L¹` norm, integrability,
pointwise bounds (hence the `L^∞` bound) and fourfold symmetry are all preserved
(`label_conservation`).
-/

@[expose] public section

open MeasureTheory Complex

namespace Euler2D

/-- **Lemma `cs:lem:conservation`** (transport part). Let `X` be a measure-preserving
measurable equivalence of `ℂ ≅ ℝ²` commuting with `x ↦ ix`, and let `ω = ω₀ ∘ X⁻¹`. Then `ω`
has the same integral and `L¹` norm as `ω₀`, is integrable if `ω₀` is, obeys every pointwise
bound obeyed by `ω₀`, and is fourfold symmetric if `ω₀` is. -/
theorem label_conservation {X : ℂ ≃ᵐ ℂ} (hX : MeasurePreserving X)
    (hrot : ∀ z, X (I * z) = I * X z) (ω₀ : ℂ → ℝ) :
    (∫ z, ω₀ (X.symm z) = ∫ z, ω₀ z) ∧
    (∫ z, |ω₀ (X.symm z)| = ∫ z, |ω₀ z|) ∧
    (Integrable ω₀ → Integrable (fun z => ω₀ (X.symm z))) ∧
    (∀ M : ℝ, (∀ z, |ω₀ z| ≤ M) → ∀ z, |ω₀ (X.symm z)| ≤ M) ∧
    ((∀ z, ω₀ (I * z) = ω₀ z) → ∀ z, ω₀ (X.symm (I * z)) = ω₀ (X.symm z)) := by
  have hXs : MeasurePreserving X.symm := hX.symm X
  have hsymm : ∀ z, X.symm (I * z) = I * X.symm z := by
    intro z
    apply X.injective
    rw [hrot, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hXs.integral_comp X.symm.measurableEmbedding ω₀
  · exact hXs.integral_comp X.symm.measurableEmbedding (fun z => |ω₀ z|)
  · intro h
    exact (hXs.integrable_comp_emb X.symm.measurableEmbedding).mpr h
  · intro M hM z
    exact hM _
  · intro hs z
    rw [hsymm, hs]

end Euler2D

end
