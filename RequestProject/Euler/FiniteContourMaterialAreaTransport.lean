module

public import RequestProject.Euler.FiniteContourParticleFlowArea

/-! The genuine finite material patch solution has an actual
area-preserving particle homeomorphism, exact transport of its real
indicator density, and preservation of every original planar Lp norm. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_finiteContour_material_area_transport
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZc : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) T))
    (hZd : ∀ t ∈ Icc (0 : ℝ) T, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ) t) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : ℂ,
        finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t x =
          finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0 ((F t).symm x)) ∧
      ∀ (p : ℝ≥0∞) t, t ∈ Icc (0 : ℝ) T →
        eLpNorm (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) p volume =
          eLpNorm (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0) p volume := by
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea⟩ := exists_finiteContour_particleFlow_area g Z Z₀ r hr href hT hsmall hZc
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  have htransport (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :=
    finiteContourPatchVorticityOnInterval_eq_initial_comp_inverse g Z Z₀ r hr href hT hsmall hZd F hF0 hFd hFinv ht x
  refine ⟨F, hFc, hFic, hF0, hFd, hFarea, htransport, ?_⟩
  intro p t ht
  have hmeas : AEStronglyMeasurable
      (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0) volume := by
    rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hT⟩]
    exact (integrable_finiteContourC1PatchVorticity g (Z 0) Z₀ r hr href (hsmall 0 ⟨le_rfl, hT⟩)).aestronglyMeasurable
  have he : finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t =
      finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0 ∘ (F t).symm := funext (htransport t ht)
  rw [he]
  exact eLpNorm_comp_measurePreserving hmeas (hFarea t ht).2

end Euler2D

end
