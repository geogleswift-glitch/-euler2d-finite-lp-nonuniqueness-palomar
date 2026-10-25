module

public import RequestProject.Euler.ContourMaterialTransport

/-! The genuine finite indicator density of the moving enclosed domains
is precisely the initial density composed with the actual inverse flow. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

theorem finiteContourPatchVorticityOnInterval_eq_initial_comp_inverse
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZ : ∀ t ∈ Icc (0 : ℝ) T, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ) t)
    (F : ℝ → ℂ ≃ₜ ℂ) (hF0 : ∀ a, F 0 a = a)
    (hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
      HasDerivAt (fun s => F s a)
        (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t)
    (hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :
    finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t x =
      finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall 0 ((F t).symm x) := by
  classical
  rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht,
    finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ⟨le_rfl, hT⟩]
  unfold finiteContourC1PatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  have he := finiteContourEnclosedDomain_eq_particleFlow_image g Z Z₀ r hr href hT hsmall
    hZ F hF0 hF hFinv ht i
  unfold contourC1PatchVorticity
  rw [← he, (F t).image_eq_preimage_symm]
  by_cases hx : (F t).symm x ∈ contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
      (hsmall 0 ⟨le_rfl, hT⟩ i) <;> simp [hx]

end Euler2D
