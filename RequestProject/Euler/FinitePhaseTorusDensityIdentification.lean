module

public import RequestProject.Euler.FinitePhaseTorusMaterialIdentification
public import RequestProject.Euler.EulerPatchTransport

/-! Exact physical indicator sums identify the original wrapped torus
transport for intrinsic domains, independently of every phase chart. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped NNReal ENNReal

namespace Euler2D

theorem phaseFiniteContourPatchVorticity_eq_physical_indicators
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) (x : R2) :
    phaseFiniteContourPatchVorticity g Z (centeredComplexHomeomorph.symm x) =
      ∑ i, g i * (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z i))).indicator
        (fun _ => (1 : ℝ)) x := by
  classical
  unfold phaseFiniteContourPatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  have hm : x ∈ complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z i)) ↔
      centeredComplexHomeomorph.symm x ∈ contourRadialFill (ContourC1Space.lift γ (Z i)) := by
    change x ∈ centeredComplexHomeomorph '' _ ↔ _
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [← hzx, Homeomorph.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨centeredComplexHomeomorph.symm x, hx, centeredComplexHomeomorph.apply_symm_apply x⟩
  unfold phaseContourPatchVorticity
  by_cases hx : centeredComplexHomeomorph.symm x ∈ contourRadialFill (ContourC1Space.lift γ (Z i))
  · rw [indicator_of_mem hx, indicator_of_mem (hm.mpr hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hm.mp h))]

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem transportedScalar_finitePhase_eq_of_domain_images
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Zstart Zend : ι → ContourC1Space γ) (v : R2 → ℝ)
    (hinit : ∀ y ∈ torusBox, v y =
      phaseFiniteContourPatchVorticity g Zstart (centeredComplexHomeomorph.symm y))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zstart i)) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i)) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zstart i))) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i)))
    {x : R2} (hx : x ∈ torusBox) :
    S.transportedScalar v t x = phaseFiniteContourPatchVorticity g Zend (centeredComplexHomeomorph.symm x) := by
  classical
  unfold transportedScalar
  rw [hinit (torusWrap (S.backward t x)) (torusRep_mem (torusProj (S.backward t x))),
    phaseFiniteContourPatchVorticity_eq_physical_indicators,
    phaseFiniteContourPatchVorticity_eq_physical_indicators]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc
    _ = (S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zstart i)))).indicator
        (fun _ => (1 : ℝ)) x :=
      S.indicator_wrapped_backward t ht (hstartbox i)
        (by rw [himages i]; exact hendbox i) 1 hx
    _ = _ := by rw [himages i]

end BoundedEulerParticleSystem
end Euler2D

end
