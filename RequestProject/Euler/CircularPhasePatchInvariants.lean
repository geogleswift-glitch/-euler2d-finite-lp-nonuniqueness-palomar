module

public import RequestProject.Euler.CircularPhaseGlobalContinuation

/-! The actual phase-independent patch has its true circulation and
fourfold symmetry. Prescribed material areas yield exactly zero
circulation for the original two-interface strengths. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem integral_phaseContourPatchVorticity {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) (b : ℝ)
    (hsmall : ‖contourParameterShiftC1 b Z - Z₀‖ ≤ r / 4) :
    (∫ x, phaseContourPatchVorticity Z x) = contourArea γ Z := by
  have hm := (isOpen_contourRadialFill_of_shift Z Z₀ hr href b hsmall).measurableSet
  rw [phaseContourPatchVorticity, integral_indicator_const _ hm, smul_eq_mul, mul_one]
  exact area_contourRadialFill_of_shift Z Z₀ hr href b hsmall

theorem integral_phaseFiniteContourPatchVorticity {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (b : ι → ℝ) (hsmall : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4) :
    (∫ x, phaseFiniteContourPatchVorticity g Z x) = ∑ i, g i * contourArea γ (Z i) := by
  have hI (i : ι) : Integrable (phaseContourPatchVorticity (Z i)) := by
    have he : phaseContourPatchVorticity (Z i) =
        contourC1PatchVorticity (contourParameterShiftC1 (b i) (Z i)) (Z₀ i) (hr i) (href i) (hsmall i) :=
      congrArg (fun D : Set ℂ => D.indicator (fun _ => (1 : ℝ)))
        (contourRadialFill_eq_enclosedDomain_of_shift (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i))
    rw [he]
    exact integrable_contourC1PatchVorticity _ _ _ _ _
  unfold phaseFiniteContourPatchVorticity
  rw [integral_finset_sum _ (fun i _ => (hI i).const_mul (g i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_phaseContourPatchVorticity (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)]

theorem circularPhasePatchVorticity_fourfold {γ : ℝ≥0} (Z : Fin 2 → LittleContourSpace γ)
    (hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) (x : ℂ) :
    circularPhasePatchVorticity Z (I * x) = circularPhasePatchVorticity Z x := by
  unfold circularPhasePatchVorticity phaseFiniteContourPatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  have hm := mul_I_mem_contourRadialFill_iff ((mem_fourfoldLittleContourSubmodule (Z i)).mp (hfour i)) x
  congr 1
  change (contourRadialFill (LittleContourSpace.lift γ (Z i))).indicator (fun _ => (1 : ℝ)) (I * x) =
    (contourRadialFill (LittleContourSpace.lift γ (Z i))).indicator (fun _ => (1 : ℝ)) x
  by_cases hx : x ∈ contourRadialFill (LittleContourSpace.lift γ (Z i))
  · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (mt hm.mp hx), indicator_of_notMem hx]

theorem integral_circularPhasePatchVorticity_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) :
    (∫ x, circularPhasePatchVorticity Z x) = 0 := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  rw [circularPhasePatchVorticity, integral_phaseFiniteContourPatchVorticity circularContourStrengths
    (fun i => (Z i).val) (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb]
  change ∑ i : Fin 2, circularContourStrengths i * littleContourArea γ (Z i) = 0
  simp_rw [harea]
  norm_num [Fin.sum_univ_two, circularContourStrengths, circularContourRadii, cellA_sq]
  <;> ring

theorem integral_circularPhasePatchPlanarVorticity_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1)
    (harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) :
    (∫ x, circularPhasePatchPlanarVorticity Z x) = 0 := by
  have he := complexPhysicalPlane.symm.measurePreserving.integral_comp
    complexPhysicalPlane.symm.toHomeomorph.measurableEmbedding (circularPhasePatchVorticity Z)
  exact he.trans (integral_circularPhasePatchVorticity_zero hγ hγ1 hZ harea)

end Euler2D

end
