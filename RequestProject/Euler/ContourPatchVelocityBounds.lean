module

public import RequestProject.Euler.ContourC1PatchVelocity
public import RequestProject.Euler.PlanarVelocityLogFlow

/-! Uniform bounds of the genuine finite patch density throughout the
quarter-radius neighborhood. The particle modulus is consequently a
proved property of the actual Biot--Savart field. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

def contourPatchMassBound (r : ℝ) : ℝ :=
  volume.real (Metric.closedBall (0 : ℂ) (5 * r / 4))

theorem integral_abs_contourC1PatchVorticity_le {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    (∫ x, |contourC1PatchVorticity Z Z₀ hr href hsmall x|) ≤ contourPatchMassBound r := by
  let D := contourC1EnclosedDomain Z Z₀ hr href hsmall
  have hm : MeasurableSet D := (isOpen_contourC1EnclosedDomain Z Z₀ hr href hsmall).measurableSet
  have he : (fun x => |contourC1PatchVorticity Z Z₀ hr href hsmall x|) =
      D.indicator (fun _ => (1 : ℝ)) := by
    funext x
    change |D.indicator (fun _ => (1 : ℝ)) x| = D.indicator (fun _ => (1 : ℝ)) x
    by_cases hx : x ∈ D <;> simp [hx]
  rw [he, integral_indicator_const _ hm, smul_eq_mul, mul_one]
  apply measureReal_mono _ (isCompact_closedBall (0 : ℂ) (5 * r / 4)).measure_ne_top
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  have hb := mem_ball_zero_iff.mp (contourC1EnclosedDomain_subset_ball Z Z₀ hr href hsmall hx)
  exact hb.le.trans (by linarith)

section Finite

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι]
  (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
  (hr : ∀ j, 0 < r j) (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
  (hsmall : ∀ j, ‖Z j - Z₀ j‖ ≤ r j / 4)

def finiteContourPatchSupBound : ℝ := ∑ j, |g j|

def finiteContourPatchMassBound : ℝ := ∑ j, |g j| * contourPatchMassBound (r j)

theorem integrable_finiteContourC1PatchVorticity :
    Integrable (finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall) :=
  integrable_finset_sum _ (fun j _ =>
    (integrable_contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j)).const_mul (g j))

theorem abs_finiteContourC1PatchVorticity_le (x : ℂ) :
    |finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall x| ≤ finiteContourPatchSupBound g := by
  unfold finiteContourC1PatchVorticity finiteContourPatchSupBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left
    (abs_contourC1PatchVorticity_le_one (Z j) (Z₀ j) (hr j) (href j) (hsmall j) x)
    (abs_nonneg _)).trans_eq (mul_one _)

theorem integral_abs_finiteContourC1PatchVorticity_le :
    (∫ x, |finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall x|) ≤
      finiteContourPatchMassBound g r := by
  have hi (j : ι) := integrable_contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j)
  have hI : Integrable (fun x => ∑ j, |g j| *
      |contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j) x|) :=
    integrable_finset_sum _ (fun j _ => (hi j).abs.const_mul _)
  calc
    _ ≤ ∫ x, ∑ j, |g j| *
        |contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j) x| := by
      apply integral_mono (integrable_finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall).abs hI
      intro x
      simpa only [finiteContourC1PatchVorticity, abs_mul] using
        Finset.abs_sum_le_sum_abs (fun j => g j *
          contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j) x) Finset.univ
    _ = ∑ j, |g j| * (∫ x, |contourC1PatchVorticity (Z j) (Z₀ j)
        (hr j) (href j) (hsmall j) x|) := by
      rw [integral_finset_sum _ (fun j _ => (hi j).abs.const_mul _)]
      simp only [integral_const_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
      (integral_abs_contourC1PatchVorticity_le (Z j) (Z₀ j) (hr j) (href j) (hsmall j))
      (abs_nonneg _))

theorem finiteContourPatchVelocity_logFlowModulus_le {x y : ℂ} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖velocityC (finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall) x -
      velocityC (finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall) y‖ ≤
      (8 * (finiteContourPatchSupBound g + finiteContourPatchMassBound g r)) *
        logFlowModulus ‖x - y‖ :=
  velocityC_logFlowModulus_le
    (integrable_finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall)
    (abs_finiteContourC1PatchVorticity_le g Z Z₀ r hr href hsmall)
    (integral_abs_finiteContourC1PatchVorticity_le g Z Z₀ r hr href hsmall) hxy

end Finite

end Euler2D
