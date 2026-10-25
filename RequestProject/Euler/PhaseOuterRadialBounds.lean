module

public import RequestProject.Euler.PhaseOuterContourForcing
public import RequestProject.Euler.RadialBiotSavartCancellation

/-! The full actual outer phase density has only cubic radial
feedback inside its core.  The potentially large circular reference
velocity is cancelled in its true singular integral. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem velocityC_sub_of_bounded {u v : ℂ → ℝ} {M N : ℝ}
    (hu : Integrable u) (hv : Integrable v) (hM : ∀ y, |u y| ≤ M) (hN : ∀ y, |v y| ≤ N)
    (z : ℂ) : velocityC (fun y => u y - v y) z = velocityC u z - velocityC v z := by
  unfold velocityC
  simp_rw [Complex.ofReal_sub, sub_mul]
  exact integral_sub (integrable_velocity_integrand hu hM z) (integrable_velocity_integrand hv hN z)

theorem abs_circlePatchVorticity_le_one (r : ℝ) (z : ℂ) : |circlePatchVorticity r z| ≤ 1 := by
  by_cases hz : z ∈ ball (0 : ℂ) r <;> simp [circlePatchVorticity, hz]

section Phase

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (Z Z₀ : ι → ContourC1Space γ) (d β : ι → ℝ)
    {c q rl : ℝ} (hc : 0 < c) (hrl : 0 < rl) (hd : ∀ i, 0 < d i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (d i * rl))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ (d i * rl) / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ rl * q)
    (hcore : ∀ i, c ≤ 3 * d i / 4)

include hc hrl hd href hsmall hq hcore

theorem phaseFiniteContourPatchPerturbation_zero_core_of_tube {x : ℂ} (hx : ‖x‖ < c * rl) :
    phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [phaseContourPatchPerturbation_zero_core (Z i) (Z₀ i) (mul_pos (hd i) hrl)
    (href i) (β i) (hsmall i) (by
      have hc' := mul_le_mul_of_nonneg_right (hcore i) hrl.le
      have hs' := hsmall i
      nlinarith)]
  exact mul_zero _

theorem integral_abs_phaseFiniteContourPatchPerturbation_le_scaled :
    (∫ x : ℂ, |phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x|) ≤
      (4 * Real.pi * ∑ i, |g i| * d i) * rl ^ 2 * q := by
  calc
    _ ≤ ∑ i, |g i| *
        (4 * Real.pi * (d i * rl) * ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖) :=
      integral_abs_phaseFiniteContourPatchPerturbation_le g Z Z₀ (fun i => d i * rl)
        (fun i => mul_pos (hd i) hrl) href β hsmall
    _ ≤ ∑ i, |g i| * (4 * Real.pi * (d i * rl) * (rl * q)) := by
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

theorem abs_radial_component_phaseFiniteContourPatchVelocity_le
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z i) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z i) θ) {x : ℂ} (hx : ‖x‖ ≤ c * rl / 2) :
    |(velocityC (phaseFiniteContourPatchVorticity g Z) x * conj x).re| ≤
      (32 / (15 * c ^ 4) * ∑ i, |g i| * d i) * q * ‖x‖ ^ 4 / rl ^ 2 := by
  let r : ι → ℝ := fun i => d i * rl
  let ref : ℂ → ℝ := fun y => ∑ i, g i * circlePatchVorticity (r i) y
  let δ := phaseFiniteContourPatchPerturbation g Z r
  have hiRef : Integrable ref := integrable_finset_sum _ fun i _ =>
    (integrable_circlePatchVorticity (r i)).const_mul _
  have hRef : ∀ y, |ref y| ≤ finiteContourPatchSupBound g := by
    intro y
    calc
      _ ≤ ∑ i, |g i| * |circlePatchVorticity (r i) y| := by
        simpa only [Real.norm_eq_abs, abs_mul] using
          norm_sum_le Finset.univ (fun i => g i * circlePatchVorticity (r i) y)
      _ ≤ ∑ i, |g i| * 1 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (abs_circlePatchVorticity_le_one _ _) (abs_nonneg _))
      _ = _ := by simp [finiteContourPatchSupBound]
  have hiPhase := integrable_phaseFiniteContourPatchVorticity g Z Z₀ r
    (fun i => mul_pos (hd i) hrl) href β hsmall
  have hPhase := abs_phaseFiniteContourPatchVorticity_le g Z Z₀ r
    (fun i => mul_pos (hd i) hrl) href β hsmall
  have he : δ = fun y => phaseFiniteContourPatchVorticity g Z y - ref y :=
    funext (phaseFiniteContourPatchPerturbation_eq_difference g Z r)
  have hvel : velocityC δ x = velocityC (phaseFiniteContourPatchVorticity g Z) x - velocityC ref x := by
    rw [he]
    exact velocityC_sub_of_bounded hiPhase hiRef hPhase hRef x
  have hrad : (velocityC (phaseFiniteContourPatchVorticity g Z) x * conj x).re =
      (velocityC δ x * conj x).re := by
    rw [hvel, sub_mul, sub_re, radial_component_finiteCirclePatchVelocity_eq_zero g r x, sub_zero]
  have hi := integrable_phaseFiniteContourPatchPerturbation g Z Z₀ r
    (fun i => mul_pos (hd i) hrl) href β hsmall
  have hz : ∀ y : ℂ, ‖y‖ < c * rl → δ y = 0 := by
    intro y hy
    exact phaseFiniteContourPatchPerturbation_zero_core_of_tube
      g Z Z₀ d β hc hrl hd href hsmall hq hcore hy
  have hm := integral_abs_phaseFiniteContourPatchPerturbation_le_scaled
    g Z Z₀ d β hc hrl hd href hsmall hq hcore
  have hp := outer_perturbation_field (mul_pos hc hrl) hi
    (phaseFiniteContourPatchPerturbation_fourfold g Z r hrot) hz hx
  have hp' : ‖velocityC δ x‖ ≤ 8 / (15 * Real.pi) * ‖x‖ ^ 3 / (c * rl) ^ 4 *
      ((4 * Real.pi * ∑ i, |g i| * d i) * rl ^ 2 * q) :=
    hp.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  calc
    _ = |(velocityC δ x * conj x).re| := by rw [hrad]
    _ ≤ ‖velocityC δ x * conj x‖ := abs_re_le_norm _
    _ = ‖velocityC δ x‖ * ‖x‖ := by rw [norm_mul, norm_conj]
    _ ≤ (8 / (15 * Real.pi) * ‖x‖ ^ 3 / (c * rl) ^ 4 *
        ((4 * Real.pi * ∑ i, |g i| * d i) * rl ^ 2 * q)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hp' (norm_nonneg _)
    _ = _ := by
      field_simp [hc.ne', hrl.ne', Real.pi_ne_zero]
      <;> ring

end Phase

end Euler2D

end
