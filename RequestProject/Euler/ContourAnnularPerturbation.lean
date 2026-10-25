module

public import RequestProject.Euler.ContourFieldSymmetry
public import RequestProject.Euler.ContourPhaseVorticity

/-! Annular support and L1 size of the actual domain perturbation.
The domains are those enclosed by the original material contours;
no radial-graph representation or area equality is an input. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def circlePatchVorticity (r : ℝ) : ℂ → ℝ := (ball 0 r).indicator (fun _ => 1)

theorem integrable_circlePatchVorticity (r : ℝ) : Integrable (circlePatchVorticity r) :=
  (integrableOn_const (measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball

theorem integral_circlePatchVorticity {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : ℂ, circlePatchVorticity r x) = Real.pi * r ^ 2 := by
  change (∫ x : ℂ, (ball 0 r).indicator 1 x) = Real.pi * r ^ 2
  rw [integral_indicator_one measurableSet_ball]
  simp [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, hr, mul_comm]

theorem circlePatchVorticity_mul_I (r : ℝ) (x : ℂ) :
    circlePatchVorticity r (I * x) = circlePatchVorticity r x := by
  have hi : I * x ∈ ball (0 : ℂ) r ↔ x ∈ ball (0 : ℂ) r := by
    simp only [mem_ball_zero_iff, norm_mul, norm_I, one_mul]
  by_cases hx : x ∈ ball (0 : ℂ) r
  · simp [circlePatchVorticity, hx, hi.mpr hx]
  · simp [circlePatchVorticity, hx, mt hi.mp hx]

theorem integral_abs_indicator_sub_circle_le_of_sandwich
    {D : Set ℂ} (hD : MeasurableSet D) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 ≤ ε) (hεr : ε ≤ r)
    (hlo : ball 0 (r - ε) ⊆ D) (hhi : D ⊆ ball 0 (r + ε)) :
    (∫ x : ℂ, |D.indicator (fun _ => (1 : ℝ)) x - circlePatchVorticity r x|) ≤
      4 * Real.pi * r * ε := by
  have hip := integrable_circlePatchVorticity (r + ε)
  have him := integrable_circlePatchVorticity (r - ε)
  have hiD : Integrable (D.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (measure_ne_top_of_subset (hhi.trans ball_subset_closedBall)
      (isCompact_closedBall (0 : ℂ) (r + ε)).measure_ne_top)).integrable_indicator hD
  have hLoRef : ball (0 : ℂ) (r - ε) ⊆ ball 0 r := ball_subset_ball (by linarith)
  have hRefHi : ball (0 : ℂ) r ⊆ ball 0 (r + ε) := ball_subset_ball (by linarith)
  have hLoHi : ball (0 : ℂ) (r - ε) ⊆ ball 0 (r + ε) := hLoRef.trans hRefHi
  have hp : ∀ x : ℂ,
      |D.indicator (fun _ => (1 : ℝ)) x - circlePatchVorticity r x| ≤
        circlePatchVorticity (r + ε) x - circlePatchVorticity (r - ε) x := by
    intro x
    by_cases hxlo : x ∈ ball (0 : ℂ) (r - ε)
    · simp [circlePatchVorticity, hxlo, hlo hxlo, hLoRef hxlo, hLoHi hxlo]
    · by_cases hxhi : x ∈ ball (0 : ℂ) (r + ε)
      · by_cases hxD : x ∈ D <;> by_cases hxref : x ∈ ball (0 : ℂ) r <;>
          simp [circlePatchVorticity, hxlo, hxhi, hxD, hxref]
      · have hxD : x ∉ D := mt (fun hx => hhi hx) hxhi
        have hxref : x ∉ ball (0 : ℂ) r := mt (fun hx => hRefHi hx) hxhi
        simp [circlePatchVorticity, hxlo, hxhi, hxD, hxref]
  calc
    _ ≤ ∫ x : ℂ, circlePatchVorticity (r + ε) x - circlePatchVorticity (r - ε) x :=
      integral_mono (hiD.sub (integrable_circlePatchVorticity r)).abs (hip.sub him) hp
    _ = 4 * Real.pi * r * ε := by
      rw [integral_sub hip him, integral_circlePatchVorticity (by linarith),
        integral_circlePatchVorticity (by linarith)]
      ring

section Contour

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (hsmall : ‖Z - Z₀‖ ≤ r / 4)

def contourC1PatchPerturbation : ℂ → ℝ :=
  fun x => contourC1PatchVorticity Z Z₀ hr href hsmall x - circlePatchVorticity r x

include hr href hsmall

theorem integrable_contourC1PatchPerturbation :
    Integrable (contourC1PatchPerturbation Z Z₀ hr href hsmall) :=
  (integrable_contourC1PatchVorticity Z Z₀ hr href hsmall).sub (integrable_circlePatchVorticity r)

theorem contourC1PatchPerturbation_zero_core {x : ℂ} (hx : ‖x‖ < r - ‖Z - Z₀‖) :
    contourC1PatchPerturbation Z Z₀ hr href hsmall x = 0 := by
  have hxlo : x ∈ ball (0 : ℂ) (r - ‖Z - Z₀‖) := mem_ball_zero_iff.mpr hx
  have hxD := ball_subset_contourC1EnclosedDomain Z Z₀ hr href hsmall hxlo
  have hxR : x ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by linarith [norm_nonneg (Z - Z₀)])
  simp [contourC1PatchPerturbation, contourC1PatchVorticity, circlePatchVorticity, hxD, hxR]

theorem contourC1PatchPerturbation_zero_outside {x : ℂ} (hx : r + ‖Z - Z₀‖ ≤ ‖x‖) :
    contourC1PatchPerturbation Z Z₀ hr href hsmall x = 0 := by
  have hxhi : x ∉ ball (0 : ℂ) (r + ‖Z - Z₀‖) := by simpa only [mem_ball_zero_iff, not_lt] using hx
  have hxD : x ∉ contourC1EnclosedDomain Z Z₀ hr href hsmall :=
    mt (fun hz => contourC1EnclosedDomain_subset_ball Z Z₀ hr href hsmall hz) hxhi
  have hxR : x ∉ ball (0 : ℂ) r := by
    simp only [mem_ball_zero_iff, not_lt]
    linarith [norm_nonneg (Z - Z₀)]
  simp [contourC1PatchPerturbation, contourC1PatchVorticity, circlePatchVorticity, hxD, hxR]

theorem integral_abs_contourC1PatchPerturbation_le :
    (∫ x : ℂ, |contourC1PatchPerturbation Z Z₀ hr href hsmall x|) ≤
      4 * Real.pi * r * ‖Z - Z₀‖ :=
  integral_abs_indicator_sub_circle_le_of_sandwich
    (isOpen_contourC1EnclosedDomain Z Z₀ hr href hsmall).measurableSet hr (norm_nonneg _)
    (by linarith) (ball_subset_contourC1EnclosedDomain Z Z₀ hr href hsmall)
    (contourC1EnclosedDomain_subset_ball Z Z₀ hr href hsmall)

theorem contourC1PatchPerturbation_fourfold
    (hrot : ∀ θ, ContourC1Space.lift γ Z (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ Z θ) (x : ℂ) :
    contourC1PatchPerturbation Z Z₀ hr href hsmall (I * x) =
      contourC1PatchPerturbation Z Z₀ hr href hsmall x := by
  unfold contourC1PatchPerturbation
  rw [contourC1PatchVorticity_mul_I Z Z₀ hr href hsmall hrot, circlePatchVorticity_mul_I]

end Contour

section Phase

variable {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (b : ℝ)
    (hsmall : ‖contourParameterShiftC1 b Z - Z₀‖ ≤ r / 4)

def phaseContourPatchPerturbation (r : ℝ) : ℂ → ℝ :=
  fun x => phaseContourPatchVorticity Z x - circlePatchVorticity r x

include hr href hsmall

theorem phaseContourPatchPerturbation_eq_shifted :
    phaseContourPatchPerturbation Z r =
      contourC1PatchPerturbation (contourParameterShiftC1 b Z) Z₀ hr href hsmall := by
  funext x
  simp only [phaseContourPatchPerturbation, contourC1PatchPerturbation,
    phaseContourPatchVorticity, contourC1PatchVorticity,
    contourRadialFill_eq_enclosedDomain_of_shift Z Z₀ hr href b hsmall]

theorem integral_abs_phaseContourPatchPerturbation_le :
    (∫ x : ℂ, |phaseContourPatchPerturbation Z r x|) ≤
      4 * Real.pi * r * ‖contourParameterShiftC1 b Z - Z₀‖ := by
  rw [phaseContourPatchPerturbation_eq_shifted Z Z₀ hr href b hsmall]
  exact integral_abs_contourC1PatchPerturbation_le _ _ _ _ _

theorem integrable_phaseContourPatchPerturbation :
    Integrable (phaseContourPatchPerturbation Z r) := by
  rw [phaseContourPatchPerturbation_eq_shifted Z Z₀ hr href b hsmall]
  exact integrable_contourC1PatchPerturbation _ _ _ _ _

theorem phaseContourPatchPerturbation_zero_core {x : ℂ}
    (hx : ‖x‖ < r - ‖contourParameterShiftC1 b Z - Z₀‖) :
    phaseContourPatchPerturbation Z r x = 0 := by
  rw [phaseContourPatchPerturbation_eq_shifted Z Z₀ hr href b hsmall]
  exact contourC1PatchPerturbation_zero_core _ _ _ _ _ hx

theorem phaseContourPatchPerturbation_zero_outside {x : ℂ}
    (hx : r + ‖contourParameterShiftC1 b Z - Z₀‖ ≤ ‖x‖) :
    phaseContourPatchPerturbation Z r x = 0 := by
  rw [phaseContourPatchPerturbation_eq_shifted Z Z₀ hr href b hsmall]
  exact contourC1PatchPerturbation_zero_outside _ _ _ _ _ hx

end Phase

theorem phaseContourPatchPerturbation_fourfold {γ : ℝ≥0} (Z : ContourC1Space γ) (r : ℝ)
    (hrot : ∀ θ, ContourC1Space.lift γ Z (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ Z θ) (x : ℂ) :
    phaseContourPatchPerturbation Z r (I * x) = phaseContourPatchPerturbation Z r x := by
  unfold phaseContourPatchPerturbation
  rw [circlePatchVorticity_mul_I]
  have hi := mul_I_mem_contourRadialFill_iff hrot x
  by_cases hx : x ∈ contourRadialFill (ContourC1Space.lift γ Z)
  · simp [phaseContourPatchVorticity, hx, hi.mpr hx]
  · simp [phaseContourPatchVorticity, hx, mt hi.mp hx]

end Euler2D

end
