module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual differentiation of contour integrals over compact parameter sets

Joint continuity supplies a genuine uniform derivative bound on the compact
product `[θ₀ - 1, θ₀ + 1] × S`.  Compactness also supplies integrability for
the base function and the constant dominator.  Differentiation under the
actual restricted-volume integral then follows from dominated local
differentiation, with no integral-derivative hypothesis.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory

namespace Euler2D

private lemma continuousOn_compactIntegral_section {S : Set ℝ} {F : ℝ → ℝ → ℂ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S)) (θ : ℝ) :
    ContinuousOn (F θ) S :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hτ => ⟨mem_univ _, hτ⟩)

/-- Genuine joint continuity on a compact integration set and genuine
pointwise derivatives give integrability of the derivative and the actual
derivative-under-integral formula. -/
theorem integrable_and_hasDerivAt_setIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) (F G : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ S))
    (hderiv : ∀ θ τ, τ ∈ S → HasDerivAt (fun t => F t τ) (G θ τ) θ)
    (θ₀ : ℝ) :
    IntegrableOn (G θ₀) S ∧
      HasDerivAt (fun θ => ∫ τ in S, F θ τ) (∫ τ in S, G θ₀ τ) θ₀ := by
  have hGcompact : ContinuousOn (Function.uncurry G)
      (Icc (θ₀ - 1) (θ₀ + 1) ×ˢ S) :=
    hG.mono (fun _ hp => ⟨mem_univ _, hp.2⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn hGcompact
  have hFmeas (θ : ℝ) : AEStronglyMeasurable (F θ) (volume.restrict S) :=
    (continuousOn_compactIntegral_section hF θ).aestronglyMeasurable hS.measurableSet
  have hFint : Integrable (F θ₀) (volume.restrict S) :=
    ContinuousOn.integrableOn_compact hS (continuousOn_compactIntegral_section hF θ₀)
  have hGmeas : AEStronglyMeasurable (G θ₀) (volume.restrict S) :=
    (continuousOn_compactIntegral_section hG θ₀).aestronglyMeasurable hS.measurableSet
  have hCint : Integrable (fun _ : ℝ => C) (volume.restrict S) :=
    integrableOn_const hS.measure_ne_top
  have hbound : ∀ᵐ τ ∂volume.restrict S, ∀ θ ∈ Ioo (θ₀ - 1) (θ₀ + 1),
      ‖G θ τ‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with τ hτ
    intro θ hθ
    exact hC (θ, τ) ⟨⟨hθ.1.le, hθ.2.le⟩, hτ⟩
  have hdiff : ∀ᵐ τ ∂volume.restrict S, ∀ θ ∈ Ioo (θ₀ - 1) (θ₀ + 1),
      HasDerivAt (fun t => F t τ) (G θ τ) θ := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with τ hτ
    intro θ _
    exact hderiv θ τ hτ
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (μ := volume.restrict S)
    (s := Ioo (θ₀ - 1) (θ₀ + 1)) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall hFmeas) hFint hGmeas hbound hCint hdiff

/-- The actual compact-parameter contour integral is differentiable, with
the integral of its actual pointwise derivative. -/
theorem hasDerivAt_setIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) (F G : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ S))
    (hderiv : ∀ θ τ, τ ∈ S → HasDerivAt (fun t => F t τ) (G θ τ) θ)
    (θ₀ : ℝ) :
    HasDerivAt (fun θ => ∫ τ in S, F θ τ) (∫ τ in S, G θ₀ τ) θ₀ :=
  (integrable_and_hasDerivAt_setIntegral_of_continuousOn_compact hS F G hF hG hderiv θ₀).2

theorem deriv_setIntegral_of_continuousOn_compact
    {S : Set ℝ} (hS : IsCompact S) (F G : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ S))
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ S))
    (hderiv : ∀ θ τ, τ ∈ S → HasDerivAt (fun t => F t τ) (G θ τ) θ)
    (θ₀ : ℝ) :
    deriv (fun θ => ∫ τ in S, F θ τ) θ₀ = ∫ τ in S, G θ₀ τ :=
  (hasDerivAt_setIntegral_of_continuousOn_compact hS F G hF hG hderiv θ₀).deriv

end Euler2D

end
