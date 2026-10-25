module

public import RequestProject.Euler.CircularPhasePatchVorticity
public import RequestProject.Euler.PlanarFourthMomentBounds

/-! The true volume moment of the phase-independent indicator
density equals the original boundary fourth moment. The complex
and real Euclidean plane formulas agree by actual measure change. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseMomentC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseMomentC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

section One

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
  (href : ContourC1Space.lift γ Z₀ = refCircle r) (b : ℝ)
  (hsmall : ‖contourParameterShiftC1 b Z - Z₀‖ ≤ r / 4)

include hr href hsmall

theorem integrable_phaseContourPatch_fourthMoment :
    Integrable (fun x : ℂ => (phaseContourPatchVorticity Z x : ℂ) * star x ^ 4) := by
  let D := contourRadialFill (ContourC1Space.lift γ Z)
  have hm : MeasurableSet D := (isOpen_contourRadialFill_of_shift Z Z₀ hr href b hsmall).measurableSet
  have hs : D ⊆ closedBall (0 : ℂ) (5 * r / 4) := fun x hx =>
    mem_closedBall_zero_iff.mpr (norm_lt_of_mem_contourRadialFill_of_shift Z Z₀ hr href b hsmall hx).le
  have hp : IntegrableOn (fun x : ℂ => star x ^ 4) D :=
    ((continuous_star.pow 4).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (5 * r / 4))).mono_set hs
  apply (hp.integrable_indicator hm).congr
  exact ae_of_all _ (fun x => by
    by_cases hx : x ∈ D <;> simp [phaseContourPatchVorticity, D, hx] at *)

theorem integral_phaseContourPatch_fourthMoment :
    (∫ x : ℂ, (phaseContourPatchVorticity Z x : ℂ) * star x ^ 4) =
      momentJ (contourRadialFill (ContourC1Space.lift γ Z)) 4 := by
  have hm := (isOpen_contourRadialFill_of_shift Z Z₀ hr href b hsmall).measurableSet
  rw [momentJ, ← integral_indicator hm]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    by_cases hx : x ∈ contourRadialFill (ContourC1Space.lift γ Z) <;>
      simp [phaseContourPatchVorticity, hx])

end One

theorem integral_phaseFiniteContourPatch_fourthMoment
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (b : ι → ℝ) (hsmall : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4) :
    (∫ x : ℂ, (phaseFiniteContourPatchVorticity g Z x : ℂ) * star x ^ 4) =
      ∑ i, (g i : ℂ) * momentJ (contourRadialFill (ContourC1Space.lift γ (Z i))) 4 := by
  have hI (i : ι) := integrable_phaseContourPatch_fourthMoment (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)
  calc
    _ = ∫ x : ℂ, ∑ i, (g i : ℂ) * ((phaseContourPatchVorticity (Z i) x : ℂ) * star x ^ 4) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [phaseFiniteContourPatchVorticity, Complex.ofReal_sum, Complex.ofReal_mul,
          Finset.sum_mul, mul_assoc])
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => (hI i).const_mul (g i : ℂ))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, integral_phaseContourPatch_fourthMoment
        (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)]

theorem planarFourthMoment_complex_density (w : ℂ → ℝ) :
    planarFourthMoment (fun x => w (complexPhysicalPlane.symm x)) = ∫ z : ℂ, (w z : ℂ) * star z ^ 4 := by
  have he := complexPhysicalPlane.measurePreserving.integral_comp
    complexPhysicalPlane.toHomeomorph.measurableEmbedding
    (fun x : R2 => (w (complexPhysicalPlane.symm x) : ℂ) * star (complexPhysicalPlane.symm x) ^ 4)
  simpa only [planarFourthMoment, planarFourthMomentIntegrand, LinearIsometryEquiv.symm_apply_apply]
    using he.symm

theorem planarFourthMoment_circularPhasePatch {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    planarFourthMoment (fun x => circularPhasePatchVorticity Z (complexPhysicalPlane.symm x)) =
      circularBoundaryFourthMoment Z := by
  rw [planarFourthMoment_complex_density]
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  rw [circularPhasePatchVorticity, integral_phaseFiniteContourPatch_fourthMoment circularContourStrengths
    (fun i => (Z i).val) (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb]
  exact (circularBoundaryFourthMoment_eq_intrinsic_domains hγ hγ1 hZ).symm

end Euler2D

end
