module

public import RequestProject.Euler.ContourAnnularPerturbation
public import RequestProject.Euler.InteriorContourForcing

/-! The actual indicators of arbitrary material phase contours give
the outer-label forcing budget in the original Little norm.  All
annular support and L1 hypotheses are derived from the true contour
distance to its circular reference. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

def phaseFiniteContourPatchPerturbation {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) (r : ι → ℝ) : ℂ → ℝ :=
  fun x => ∑ i, g i * phaseContourPatchPerturbation (Z i) (r i) x

theorem phaseFiniteContourPatchPerturbation_eq_difference {γ : ℝ≥0}
    {ι : Type*} [Fintype ι] (g : ι → ℝ) (Z : ι → ContourC1Space γ) (r : ι → ℝ) (x : ℂ) :
    phaseFiniteContourPatchPerturbation g Z r x =
      phaseFiniteContourPatchVorticity g Z x - ∑ i, g i * circlePatchVorticity (r i) x := by
  simp only [phaseFiniteContourPatchPerturbation, phaseContourPatchPerturbation,
    phaseFiniteContourPatchVorticity, mul_sub, Finset.sum_sub_distrib]

section Geometry

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (b : ι → ℝ)
    (hsmall : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4)

include hr href hsmall

theorem integrable_phaseFiniteContourPatchPerturbation :
    Integrable (phaseFiniteContourPatchPerturbation g Z r) :=
  integrable_finset_sum _ fun i _ =>
    (integrable_phaseContourPatchPerturbation (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)).const_mul _

theorem integral_abs_phaseFiniteContourPatchPerturbation_le :
    (∫ x : ℂ, |phaseFiniteContourPatchPerturbation g Z r x|) ≤
      ∑ i, |g i| * (4 * Real.pi * r i * ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖) := by
  have hi (i : ι) := integrable_phaseContourPatchPerturbation
    (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)
  calc
    _ ≤ ∫ x : ℂ, ∑ i, |g i| * |phaseContourPatchPerturbation (Z i) (r i) x| := by
      apply integral_mono
        (integrable_phaseFiniteContourPatchPerturbation g Z Z₀ r hr href b hsmall).abs
        (integrable_finset_sum _ (fun i _ => (hi i).abs.const_mul _))
      intro x
      simpa only [phaseFiniteContourPatchPerturbation, Real.norm_eq_abs, abs_mul] using
        norm_sum_le Finset.univ (fun i => g i * phaseContourPatchPerturbation (Z i) (r i) x)
    _ = ∑ i, |g i| * ∫ x : ℂ, |phaseContourPatchPerturbation (Z i) (r i) x| := by
      rw [integral_finset_sum _ (fun i _ => (hi i).abs.const_mul _)]
      simp only [integral_const_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (integral_abs_phaseContourPatchPerturbation_le (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i))
      (abs_nonneg _))

end Geometry

theorem phaseFiniteContourPatchPerturbation_fourfold {γ : ℝ≥0}
    {ι : Type*} [Fintype ι] (g : ι → ℝ) (Z : ι → ContourC1Space γ) (r : ι → ℝ)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z i) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z i) θ) (x : ℂ) :
    phaseFiniteContourPatchPerturbation g Z r (I * x) = phaseFiniteContourPatchPerturbation g Z r x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [phaseContourPatchPerturbation_fourfold (Z i) (r i) (hrot i)]

/-- This is the actual original material-phase patch minus its circular
reference, rather than a forcing whose source estimates are assumed. -/
theorem exists_phaseOuterLabelContourFieldLittle_ratio {γ η : ℝ≥0}
    (hη : (η : ℝ) ≤ 1) {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (d b : ι → ℝ)
    {A c B q rl rj L : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hrl : 0 < rl) (hrj : 0 < rj)
    (hd : ∀ i, 0 < d i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (d i * rl))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ (d i * rl) / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ rl * q)
    (hcore : ∀ i, c ≤ 3 * d i / 4)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z i) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z i) θ)
    (hsep : 8 * (B * rj) ≤ c * rl)
    (W : LittleContourSpace η) (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * rj)
    (hL : ‖W‖ ≤ rj * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (fun x => A * phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / rj ≤ interiorContourNormBudget (η : ℝ) 1 c B L *
        (4 * Real.pi * |A| * ∑ i, |g i| * d i) * (rj / rl) ^ 2 * q := by
  have hi := integrable_phaseFiniteContourPatchPerturbation g Z Z₀ (fun i => d i * rl)
    (fun i => mul_pos (hd i) hrl) href b hsmall
  have hzero : ∀ x, ‖x‖ < c * rl →
      (fun x => A * phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x) x = 0 := by
    intro x hx
    change A * phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x = 0
    suffices phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x = 0 by rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro i _
    rw [phaseContourPatchPerturbation_zero_core (Z i) (Z₀ i) (mul_pos (hd i) hrl)
      (href i) (b i) (hsmall i) (by
        have hc' := mul_le_mul_of_nonneg_right (hcore i) hrl.le
        have hs' := hsmall i
        nlinarith)]
    exact mul_zero _
  have hmass : (∫ x : ℂ, |A * phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x|) ≤
      (4 * Real.pi * |A| * ∑ i, |g i| * d i) * rl ^ 2 * q := by
    simp_rw [abs_mul]
    rw [integral_const_mul]
    calc
      _ ≤ |A| * ∑ i, |g i| *
          (4 * Real.pi * (d i * rl) * ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖) :=
        mul_le_mul_of_nonneg_left
          (integral_abs_phaseFiniteContourPatchPerturbation_le g Z Z₀ (fun i => d i * rl)
            (fun i => mul_pos (hd i) hrl) href b hsmall) (abs_nonneg _)
      _ ≤ |A| * ∑ i, |g i| * (4 * Real.pi * (d i * rl) * (rl * q)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        have hdi := hd i
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hq i) (by positivity)) (abs_nonneg _)
      _ = _ := by
        simp_rw [show ∀ i : ι, |g i| * (4 * Real.pi * (d i * rl) * (rl * q)) =
          (4 * Real.pi * rl ^ 2 * q) * (|g i| * d i) by intro i; ring]
        rw [← Finset.mul_sum]
        ring
  apply exists_outerLabelContourFieldLittle_ratio hη hc hB hrl hrj (hi.const_mul A)
    (fun x => by rw [phaseFiniteContourPatchPerturbation_fourfold g Z _ hrot])
    hzero hmass hsep W hW hL

end Euler2D

end
