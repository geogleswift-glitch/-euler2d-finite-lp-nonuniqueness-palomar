module

public import RequestProject.Euler.ContourPatchBoundaryVelocity
public import RequestProject.Euler.ContourC1EnclosedDomain
public import RequestProject.Euler.ContourCauchyIncrement
public import RequestProject.Euler.ContourBoundaryField
public import RequestProject.Euler.LogLipschitz

/-! The original finite-interface field is the actual Biot–Savart
velocity of the actual domains constructed from C¹ loops. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

theorem lt_circle_chord_of_quarter_radius {r ε : ℝ} (hr : 0 < r) (hε : ε ≤ r / 4) :
    ε < 2 * r / Real.pi := by
  have hp : Real.pi < 8 := Real.pi_lt_four.trans (by norm_num)
  have hm := mul_pos hr (sub_pos.mpr hp)
  have h : r / 4 < 2 * r / Real.pi := (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith)
  exact hε.trans_lt h

def contourC1PatchVorticity {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) : ℂ → ℝ :=
  (contourC1EnclosedDomain Z Z₀ hr href hsmall).indicator (fun _ => 1)

theorem integrable_contourC1PatchVorticity {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) :
    Integrable (contourC1PatchVorticity Z Z₀ hr href hsmall) := by
  have hm := (isOpen_contourC1EnclosedDomain Z Z₀ hr href hsmall).measurableSet
  have hfinite : volume (contourC1EnclosedDomain Z Z₀ hr href hsmall) ≠ ⊤ :=
    measure_ne_top_of_subset ((contourC1EnclosedDomain_subset_ball Z Z₀ hr href hsmall).trans
      Metric.ball_subset_closedBall) (isCompact_closedBall (0 : ℂ) (r + ‖Z - Z₀‖)).measure_ne_top
  exact (integrableOn_const hfinite).integrable_indicator hm

theorem abs_contourC1PatchVorticity_le_one {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) (x : ℂ) :
    |contourC1PatchVorticity Z Z₀ hr href hsmall x| ≤ 1 := by
  by_cases hx : x ∈ contourC1EnclosedDomain Z Z₀ hr href hsmall <;>
    simp [contourC1PatchVorticity, hx]

theorem velocityC_contourC1PatchVorticity {γ : ℝ≥0} (Z Z₀ : ContourC1Space γ) {r : ℝ}
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) (x : ℂ) :
    velocityC (contourC1PatchVorticity Z Z₀ hr href hsmall) x =
      (-1 / (2 * Real.pi) : ℂ) * contourLogBoundaryIntegral
        (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) x := by
  have hdp : Function.Periodic (deriv (ContourC1Space.lift γ Z)) (2 * Real.pi) := by
    intro θ
    rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift, AddCircle.coe_add_period]
  exact velocityC_nearCircleEnclosedDomain_eq_boundaryIntegral hr (norm_nonneg _) hsmall
    (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
    (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2
    (ContourC1Space.periodic_lift Z) hdp
    (sub_pos.mpr (lt_circle_chord_of_quarter_radius hr hsmall))
    (fun θ => ContourC1Space.norm_eval_le Z (θ : ContourCircle))
    (ContourC1Space.norm_deriv_lift_le Z)
    (fun θ τ hτ => contourC1_chord_lower_of_norm_sub Z Z₀ hr.le href θ (abs_le.mp hτ)) x

theorem velocityC_finite_sum_smul {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (f : ι → ℂ → ℝ) (M : ι → ℝ)
    (hf : ∀ j, Integrable (f j)) (hM : ∀ j y, |f j y| ≤ M j) (x : ℂ) :
    velocityC (fun y => ∑ j, g j * f j y) x = ∑ j, (g j : ℂ) * velocityC (f j) x := by
  unfold velocityC
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
  simp_rw [← integral_const_mul]
  apply integral_finset_sum
  intro j _
  simpa only [mul_assoc] using
    (integrable_velocity_integrand (hf j) (hM j) x).const_mul (g j : ℂ)

def finiteContourC1PatchVorticity {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ j, 0 < r j) (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    (hsmall : ∀ j, ‖Z j - Z₀ j‖ ≤ r j / 4) : ℂ → ℝ :=
  fun x => ∑ j, g j * contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j) x

theorem contourC1BoundaryField_eq_actual_velocity {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ j, 0 < r j) (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    (hsmall : ∀ j, ‖Z j - Z₀ j‖ ≤ r j / 4) (i : ι) (θ : ℝ) :
    contourC1BoundaryField g Z i θ =
      velocityC (finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall)
        (ContourC1Space.lift γ (Z i) θ) := by
  unfold finiteContourC1PatchVorticity
  rw [velocityC_finite_sum_smul g _ (fun _ => 1)
    (fun j => integrable_contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j))
    (fun j => abs_contourC1PatchVorticity_le_one (Z j) (Z₀ j) (hr j) (href j) (hsmall j))]
  simp_rw [velocityC_contourC1PatchVorticity]
  unfold contourC1BoundaryField contourBoundaryField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Euler2D
