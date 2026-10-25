module

public import RequestProject.Euler.ContourCauchyLocusCircle

/-! # Uniform limits of the actual Cauchy increment -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

/-- Convergence of the genuine curve and density norms gives uniform
convergence of the literal singular increment on every real angle. -/
theorem tendstoUniformly_contourC1CauchyIncrement {γ : ℝ≥0} {ι : Type*}
    (hγ : 0 < (γ : ℝ)) {l : Filter ι}
    (Z : ι → ContourC1Space γ) (Z₀ : ContourC1Space γ)
    (f : ι → ContourHolderSpace γ) (f₀ : ContourHolderSpace γ)
    (hZ : ∀ n, ContourC1Space.HasPositiveChordArc (Z n))
    (hZ₀ : ContourC1Space.HasPositiveChordArc Z₀)
    (hZlim : Tendsto Z l (𝓝 Z₀)) (hflim : Tendsto f l (𝓝 f₀)) :
    TendstoUniformly (fun n θ => contourC1CauchyIncrement (Z n) (f n) θ)
      (contourC1CauchyIncrement Z₀ f₀) l := by
  let p : ι → {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
      ContourHolderSpace γ := fun n => (⟨Z n, hZ n⟩, f n)
  let p₀ : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z} ×
      ContourHolderSpace γ := (⟨Z₀, hZ₀⟩, f₀)
  have hz : Tendsto (fun n => (⟨Z n, hZ n⟩ :
      {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z})) l
      (𝓝 (⟨Z₀, hZ₀⟩ : {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z})) :=
    tendsto_subtype_rng.mpr hZlim
  have hp : Tendsto p l (𝓝 p₀) := hz.prodMk_nhds hflim
  have hb : Tendsto (fun n => contourCauchyIncrementBCF hγ (p n)) l
      (𝓝 (contourCauchyIncrementBCF hγ p₀)) :=
    (continuous_contourCauchyIncrementBCF hγ).continuousAt.tendsto.comp hp
  have hu : TendstoUniformly
      (fun n x => contourCauchyIncrementBCF hγ (p n) x)
      (fun x => contourCauchyIncrementBCF hγ p₀ x) l :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hb
  simpa only [Function.comp_def, contourCauchyIncrementBCF_coe, p, p₀] using
    hu.comp (fun θ : ℝ => (θ : ContourCircle))

end Euler2D

end
