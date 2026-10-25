module

public import RequestProject.Euler.PlanarKernelRegularization
public import RequestProject.Euler.ContourPatchVelocityBounds
public import RequestProject.Euler.ContourC1GreenFormula

/-! Joint continuity of the actual patch velocity as the true C¹
contour varies. A regularized Green integral is continuous on its fixed
parameter interval, and the planar kernel estimate is uniform in space. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal UniformConvergence

namespace Euler2D

def contourC1RegularizedPatchVelocity {γ : ℝ≥0} (Z : ContourC1Space γ)
    (δ : ℝ) (x : ℂ) : ℂ :=
  (-1 / (2 * Real.pi) : ℂ) * contourRegularizedLogBoundaryIntegral
    (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) δ x

def contourPatchVelocityApproximationBound (r : ℝ) : ℝ :=
  ‖(-I / (2 * Real.pi) : ℂ)‖ * (4 * Real.pi + contourPatchMassBound r)

theorem contourC1RegularizedPatchVelocity_eq_gradient {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r δ : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) (hδ : δ ≠ 0) (x : ℂ) :
    contourC1RegularizedPatchVelocity Z δ x = (-I / (2 * Real.pi) : ℂ) *
      (∫ y in contourC1EnclosedDomain Z Z₀ hr href hsmall, regularizedLogGradient x δ y) := by
  have hg := integral_gradient_contourC1EnclosedDomain Z Z₀ hr href hsmall
    (hasFDerivAt_regularizedLogPotential x hδ) (continuous_regularizedLogPotentialDerivative x hδ)
  have he : (∫ y in contourC1EnclosedDomain Z Z₀ hr href hsmall, regularizedLogGradient x δ y) =
      -I * contourRegularizedLogBoundaryIntegral (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) δ x := by
    simpa only [complexRealGradient_regularizedLogPotentialDerivative, regularizedLogPotential,
      contourRegularizedLogBoundaryIntegral, Complex.real_smul, norm_sub_rev] using hg
  rw [he]
  unfold contourC1RegularizedPatchVelocity
  ring_nf <;> simp only [I_sq] <;> ring

theorem norm_contourC1PatchVelocity_sub_regularized_le {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r s : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z - Z₀‖ ≤ r / 4) (hs : 0 < s) (x : ℂ) :
    ‖velocityC (contourC1PatchVorticity Z Z₀ hr href hsmall) x -
      contourC1RegularizedPatchVelocity Z (s ^ 2) x‖ ≤
      contourPatchVelocityApproximationBound r * s := by
  let D := contourC1EnclosedDomain Z Z₀ hr href hsmall
  have hm : MeasurableSet D := (isOpen_contourC1EnclosedDomain Z Z₀ hr href hsmall).measurableSet
  have hsubset : D ⊆ Metric.closedBall (0 : ℂ) (r + ‖Z - Z₀‖) :=
    (contourC1EnclosedDomain_subset_ball Z Z₀ hr href hsmall).trans Metric.ball_subset_closedBall
  have hi (δ : ℝ) : IntegrableOn (regularizedLogGradient x δ) D :=
    integrableOn_regularizedLogGradient_of_subset_closedBall
      (add_nonneg hr.le (norm_nonneg _)) hsubset x δ
  have ho : velocityC (contourC1PatchVorticity Z Z₀ hr href hsmall) x =
      (-I / (2 * Real.pi) : ℂ) * ∫ y in D, regularizedLogGradient x 0 y := by
    simpa only [contourC1PatchVorticity, regularizedLogGradient, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_add] using velocityC_indicator_eq_logGradient hm x
  have he : velocityC (contourC1PatchVorticity Z Z₀ hr href hsmall) x -
      contourC1RegularizedPatchVelocity Z (s ^ 2) x =
      (-I / (2 * Real.pi) : ℂ) * (∫ y, (contourC1PatchVorticity Z Z₀ hr href hsmall y : ℂ) *
        (regularizedLogGradient x 0 y - regularizedLogGradient x (s ^ 2) y)) := by
    rw [ho, contourC1RegularizedPatchVelocity_eq_gradient Z Z₀ hr href hsmall (pow_ne_zero 2 hs.ne')]
    have hfn : (fun y => (contourC1PatchVorticity Z Z₀ hr href hsmall y : ℂ) *
        (regularizedLogGradient x 0 y - regularizedLogGradient x (s ^ 2) y)) =
        D.indicator (fun y => regularizedLogGradient x 0 y - regularizedLogGradient x (s ^ 2) y) := by
      funext y
      change ((D.indicator (fun _ => (1 : ℝ)) y : ℝ) : ℂ) * _ = _
      by_cases hy : y ∈ D <;> simp [hy]
    rw [hfn, integral_indicator hm, integral_sub (hi 0) (hi (s ^ 2))]
    ring
  rw [he, norm_mul]
  have hb := norm_integral_regularizedLogGradient_error_le
    (integrable_contourC1PatchVorticity Z Z₀ hr href hsmall)
    (abs_contourC1PatchVorticity_le_one Z Z₀ hr href hsmall) hs x
  have hmass := integral_abs_contourC1PatchVorticity_le Z Z₀ hr href hsmall
  have herr : ‖∫ y, (contourC1PatchVorticity Z Z₀ hr href hsmall y : ℂ) *
      (regularizedLogGradient x 0 y - regularizedLogGradient x (s ^ 2) y)‖ ≤
      (4 * Real.pi + contourPatchMassBound r) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hmass hs.le]
  exact (mul_le_mul_of_nonneg_left herr (norm_nonneg _)).trans_eq (by
    unfold contourPatchVelocityApproximationBound
    ring)

theorem continuous_contourC1RegularizedPatchVelocity {P : Type*} [TopologicalSpace P]
    {γ : ℝ≥0} {Z : P → ContourC1Space γ} (hZ : Continuous Z)
    {δ : ℝ} (hδ : δ ≠ 0) :
    Continuous (fun p : P × ℂ => contourC1RegularizedPatchVelocity (Z p.1) δ p.2) := by
  have hz : Continuous (fun q : (P × ℂ) × ℝ => ContourC1Space.lift γ (Z q.1.1) q.2) := by
    exact continuous_eval.comp (((ContourC1Space.toBCF γ).continuous.comp
      (hZ.comp (continuous_fst.comp continuous_fst))).prodMk
        ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd))
  have hd : Continuous (fun q : (P × ℂ) × ℝ =>
      deriv (ContourC1Space.lift γ (Z q.1.1)) q.2) := by
    simp_rw [ContourC1Space.deriv_lift]
    exact continuous_eval.comp ((((HolderFunctionSpace.toBCF γ).continuous.comp
      (ContourC1Space.derivative γ).continuous).comp
        (hZ.comp (continuous_fst.comp continuous_fst))).prodMk
          ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd))
  have hp : Continuous (fun q : (P × ℂ) × ℝ =>
      ((1 / 2 : ℝ) * Real.log (δ ^ 2 + ‖q.1.2 - ContourC1Space.lift γ (Z q.1.1) q.2‖ ^ 2)) •
        deriv (ContourC1Space.lift γ (Z q.1.1)) q.2) := by
    have hn := (continuous_snd.comp continuous_fst).sub hz
    have hlog := (continuous_const.add (hn.norm.pow 2)).log (fun q =>
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hδ) (sq_nonneg _)).ne')
    exact (continuous_const.mul hlog).smul hd
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := (0 : ℝ)) hp continuous_const)

end Euler2D
