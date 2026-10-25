module

public import RequestProject.Euler.FiniteContourTorusMaterialIdentification
public import RequestProject.Euler.EulerPatchTransport

/-! Literal finite patch densities for the original torus particle flow.
The physical image domains, including their confinement to the torus box,
identify wrapped transport with the actual contour indicator sum. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped NNReal ENNReal

namespace Euler2D

theorem finiteContourC1PatchVorticity_eq_physical_indicators
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hsmall : ∀ i, ‖Z i - Z₀ i‖ ≤ r i / 4) (x : R2) :
    finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall
        (centeredComplexHomeomorph.symm x) =
      ∑ i, g i * (complexTorusPoint ''
        contourC1EnclosedDomain (Z i) (Z₀ i) (hr i) (href i) (hsmall i)).indicator
          (fun _ => (1 : ℝ)) x := by
  classical
  unfold finiteContourC1PatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  have hm : x ∈ complexTorusPoint ''
      contourC1EnclosedDomain (Z i) (Z₀ i) (hr i) (href i) (hsmall i) ↔
      centeredComplexHomeomorph.symm x ∈
        contourC1EnclosedDomain (Z i) (Z₀ i) (hr i) (href i) (hsmall i) := by
    change x ∈ centeredComplexHomeomorph '' _ ↔ _
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [← hzx, Homeomorph.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨centeredComplexHomeomorph.symm x, hx, centeredComplexHomeomorph.apply_symm_apply x⟩
  unfold contourC1PatchVorticity
  by_cases hx : centeredComplexHomeomorph.symm x ∈
      contourC1EnclosedDomain (Z i) (Z₀ i) (hr i) (href i) (hsmall i)
  · rw [indicator_of_mem hx, indicator_of_mem (hm.mpr hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hm.mp h))]

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem transportedScalar_finiteContour_eq_of_domain_images
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Zstart Zend Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hstart : ∀ i, ‖Zstart i - Z₀ i‖ ≤ r i / 4)
    (hend : ∀ i, ‖Zend i - Z₀ i‖ ≤ r i / 4)
    (v : R2 → ℝ)
    (hinit : ∀ y ∈ torusBox, v y =
      finiteContourC1PatchVorticity g Zstart Z₀ r hr href hstart
        (centeredComplexHomeomorph.symm y))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : ∀ i, complexTorusPoint ''
      contourC1EnclosedDomain (Zstart i) (Z₀ i) (hr i) (href i) (hstart i) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint ''
      contourC1EnclosedDomain (Zend i) (Z₀ i) (hr i) (href i) (hend i) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint ''
      contourC1EnclosedDomain (Zstart i) (Z₀ i) (hr i) (href i) (hstart i)) =
      complexTorusPoint '' contourC1EnclosedDomain (Zend i) (Z₀ i) (hr i) (href i) (hend i))
    {x : R2} (hx : x ∈ torusBox) :
    S.transportedScalar v t x = finiteContourC1PatchVorticity g Zend Z₀ r hr href hend
      (centeredComplexHomeomorph.symm x) := by
  classical
  unfold transportedScalar
  rw [hinit (torusWrap (S.backward t x)) (torusRep_mem (torusProj (S.backward t x))),
    finiteContourC1PatchVorticity_eq_physical_indicators,
    finiteContourC1PatchVorticity_eq_physical_indicators]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc
    _ = (S.forward t '' (complexTorusPoint ''
        contourC1EnclosedDomain (Zstart i) (Z₀ i) (hr i) (href i) (hstart i))).indicator
          (fun _ => (1 : ℝ)) x :=
      S.indicator_wrapped_backward t ht (hstartbox i)
        (by rw [himages i]; exact hendbox i) 1 hx
    _ = _ := by rw [himages i]

end BoundedEulerParticleSystem
end Euler2D

end
