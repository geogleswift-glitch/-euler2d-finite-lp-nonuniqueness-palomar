module

public import RequestProject.Euler.ContourDomainTransport
public import RequestProject.Euler.LogFlowIntervalUniqueness
public import RequestProject.Euler.ContourPatchVelocityBounds

/-! Actual material transport of the enclosed finite patch domains.
The boundary trajectories are identified by the proved logarithmic
particle uniqueness, and the full domains by the inverse isotopy. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

def finiteContourPatchVorticityOnInterval
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (t : ℝ) : ℂ → ℝ :=
  if ht : t ∈ Icc (0 : ℝ) T then
    finiteContourC1PatchVorticity g (Z t) Z₀ r hr href (hsmall t ht)
  else fun _ => 0

theorem finiteContourPatchVorticityOnInterval_of_mem
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {T : ℝ} (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t =
      finiteContourC1PatchVorticity g (Z t) Z₀ r hr href (hsmall t ht) := by
  simp only [finiteContourPatchVorticityOnInterval, dif_pos ht]

section Material

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι]
  (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
  (r : ι → ℝ) (hr : ∀ i, 0 < r i)
  (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
  {T : ℝ} (hT : 0 ≤ T)
  (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
  (hZ : ∀ t ∈ Icc (0 : ℝ) T, ∀ i θ,
    HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
      (contourC1BoundaryField g (Z t) i θ) t)
  (F : ℝ → ℂ ≃ₜ ℂ)
  (hF0 : ∀ a, F 0 a = a)
  (hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    HasDerivAt (fun s => F s a)
      (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a)) t)

include hZ hF0 hF hT

theorem finiteContourBoundary_eq_particleFlow
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : ι) (θ : ℝ) :
    F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ := by
  let v : ℝ → ℂ → ℂ := fun s =>
    velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall s)
  have hdloop (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun q => ContourC1Space.lift γ (Z q i) θ)
        (v s (ContourC1Space.lift γ (Z s i) θ)) s := by
    have hd := hZ s hs i θ
    rw [contourC1BoundaryField_eq_actual_velocity g (Z s) Z₀ r hr href (hsmall s hs)] at hd
    simpa only [v, finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall hs] using hd
  have hC : 0 ≤ 8 * (finiteContourPatchSupBound g + finiteContourPatchMassBound g r) := by
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  have hlip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (x y : ℂ) (hxy : ‖x - y‖ ≤ 1 / 2) :
      ‖v s x - v s y‖ ≤ (8 * (finiteContourPatchSupBound g + finiteContourPatchMassBound g r)) *
        logFlowModulus ‖x - y‖ := by
    dsimp only [v]
    rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall hs]
    exact finiteContourPatchVelocity_logFlowModulus_le g (Z s) Z₀ r hr href (hsmall s hs) hxy
  exact logFlow_uniqueOn hC
    (fun s hs => (hF s hs _).continuousAt.continuousWithinAt)
    (fun s hs => (hdloop s hs).continuousAt.continuousWithinAt)
    (fun s hs => hF s hs _) hdloop (hF0 _) hlip t ht

theorem finiteContourEnclosedDomain_eq_particleFlow_image
    (hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : ι) :
    F t '' contourC1EnclosedDomain (Z 0 i) (Z₀ i) (hr i) (href i)
      (hsmall 0 ⟨le_rfl, hT⟩ i) =
      contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i) := by
  apply image_contourC1EnclosedDomain_of_boundary_isotopy (fun s => Z s i) (Z₀ i)
    (hr i) hT (href i) (fun s hs => hsmall s hs i) F hFinv
  · rw [← hF0 ((F 0).symm 0), (F 0).apply_symm_apply]
  · intro s hs θ
    exact finiteContourBoundary_eq_particleFlow g Z Z₀ r hr href hT hsmall hZ F hF0 hF hs i θ
  · exact ht

end Material

end Euler2D
