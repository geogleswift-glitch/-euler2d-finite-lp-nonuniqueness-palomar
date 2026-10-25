module

public import RequestProject.Euler.FiniteContourParticleFlow

/-! The actual finite material equation determines a real common
particle homeomorphism flow, the enclosed domains and their densities.
No particle-flow existence hypothesis remains in this statement. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_finiteContour_actual_material_transport
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) T))
    (hmat : ∀ t ∈ Icc (0 : ℝ) T, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ) t) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t) ∧
      ∀ t (ht : t ∈ Icc (0 : ℝ) T),
        (∀ i θ, F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ) ∧
        (∀ i, F t '' contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
            (hsmall 0 ⟨le_rfl, hT⟩ i) =
          contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i)) ∧
        ∀ x, finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t x =
          finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0 ((F t).symm x) := by
  obtain ⟨F, hFc, hFic, hF0, hFd⟩ :=
    exists_finiteContour_particleFlow g Z Z₀ r hr href hT hsmall hZ
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨F, hFc, hFic, hF0, hFd, ?_⟩
  intro t ht
  exact ⟨fun i θ => finiteContourBoundary_eq_particleFlow g Z Z₀ r hr href hT hsmall hmat
      F hF0 hFd ht i θ,
    fun i => finiteContourEnclosedDomain_eq_particleFlow_image g Z Z₀ r hr href hT hsmall hmat
      F hF0 hFd hFinv ht i,
    fun x => finiteContourPatchVorticityOnInterval_eq_initial_comp_inverse g Z Z₀ r hr href hT
      hsmall hmat F hF0 hFd hFinv ht x⟩

end Euler2D

end
